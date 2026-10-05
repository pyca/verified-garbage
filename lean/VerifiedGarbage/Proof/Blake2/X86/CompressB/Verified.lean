import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Blake2.X86.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Impl.Blake2.X86.CompressB
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressB.G`. -/
section

/-!
# BLAKE2b on x86 (32-bit): `G`

The weakest-precondition rules for the 64-bit operations of
`VG.Impl.Blake2.X86.CompressB` that `Proof/Sha512/X86/Rounds.lean` does not
have (the exclusive or of two pairs, and the rotations), and `g_ok`: one
symbolic execution of `G` for any offsets of its words in `scratch`.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86
open VG.Impl.Blake2.X86.CompressB (xor64 mask rorPair g)
open VG.Impl.Sha512.X86 (ld st add64 add64m)
open VG.Proof.Sha512.X86 (Only Pair Acc rd64 write64 wp_ld wp_st wp_add64 wp_add64m wp_xorS
  wp_andS wp_movS wp_ror rd64_write64_self rd64_write64_ne frame_write64)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_rotr hi_rotr lo_rotr' hi_rotr')
open VG.Proof.Sha256.X86.Stream (Upd Mupd)

/-! ## Rotations of 64-bit words as pairs -/

/-- What `rorPair` computes in one half: `Q` rotated by `k`, with its low
`32 - k` bits replaced by those of `P` rotated by `k`. -/
def merge (P Q : BitVec 32) (k : Nat) : BitVec 32 :=
  Q.rotateRight k ^^^ ((P.rotateRight k ^^^ Q.rotateRight k) &&& mask k)

theorem merge_eq (P Q : BitVec 32) {k : Nat} (h0 : 0 < k) (h : k < 32) :
    VG.Proof.Blake2.X86.CompressB.merge P Q k = P >>> k ^^^ Q <<< (32 - k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [VG.Proof.Blake2.X86.CompressB.merge, mask, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    Nat.mod_eq_of_lt h]
  by_cases hc : i < 32 - k
  · simp [hc, hi, show k + i < 32 by omega]
    cases P[k + i] <;> cases Q[k + i] <;> rfl
  · simp [hc, hi, show ¬ k + i < 32 by omega, BitVec.getLsbD_of_ge P (k + i) (by omega)]

theorem lo_rotr32 (x : BitVec 64) : lo (x.rotateRight 32) = hi x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi']

theorem hi_rotr32 (x : BitVec 64) : hi (x.rotateRight 32) = lo x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [lo, hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_rotateRight]
  simp [hi', show ¬ 32 + i < 32 by omega, show 32 + i - 32 = i by omega, show 32 + i < 64 by omega]

/-- A rotation by 32 swaps the halves. -/
theorem _root_.VG.Proof.Sha512.X86.Pair.swap {s : State} {l h : Reg} {x : BitVec 64} (p : Pair s l h x) :
    Pair s h l (x.rotateRight 32) :=
  ⟨by rw [VG.Proof.Blake2.X86.CompressB.lo_rotr32]; exact p.2, by rw [VG.Proof.Blake2.X86.CompressB.hi_rotr32]; exact p.1⟩

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : Pair s dl dh x) (py : Pair s l h y)
    (k : ∀ s', Only [dl, dh] s s' → Pair s' dl dh (x ^^^ y) → WP isa (.block rest) s' Q) :
    WP isa (.block (xor64 dl dh l h ++ rest)) s Q := by
  simp only [xor64, List.cons_append, List.nil_append]
  refine wp_xorS rfl fun s₁ u₁ => ?_
  refine wp_xorS rfl fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_xor]
  · rw [u₂.gpr, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.2, py.2, hi_xor]

theorem wp_rorPair {l h t : Reg} {k : Nat} (h0 : 0 < k) (hk : k < 32) (hlh : l ≠ h) (hlt : l ≠ t)
    (hht : h ≠ t) {P R : BitVec 32} (hl : s.gpr l = P) (hh : s.gpr h = R)
    (K : ∀ s', Only [l, h, t] s s' → s'.gpr h = VG.Proof.Blake2.X86.CompressB.merge P R k → s'.gpr l = VG.Proof.Blake2.X86.CompressB.merge R P k →
      WP isa (.block rest) s' Q) :
    WP isa (.block (rorPair l h k t ++ rest)) s Q := by
  simp only [rorPair, List.cons_append, List.nil_append]
  refine wp_ror ⟨h0, by omega⟩ fun s₁ u₁ => wp_ror ⟨h0, by omega⟩ fun s₂ u₂ =>
    wp_movS rfl fun s₃ u₃ => wp_xorS rfl fun s₄ u₄ => wp_andS rfl fun s₅ u₅ =>
    wp_xorS rfl fun s₆ u₆ => wp_xorS rfl fun s₇ u₇ => ?_
  have O := (((((((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans
    (Only.of_upd u₄)).trans (Only.of_upd u₅)).trans (Only.of_upd u₆)).trans (Only.of_upd u₇))
  -- The rotated halves, and the mask of their bits to exchange.
  have eL : s₂.gpr l = P.rotateRight k := by rw [u₂.other _ hlh, u₁.gpr, hl]
  have eH : s₂.gpr h = R.rotateRight k := by rw [u₂.gpr, u₁.other _ (Ne.symm hlh), hh]
  have eT : s₅.gpr t = (P.rotateRight k ^^^ R.rotateRight k) &&& mask k := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ hht, eL, eH]
  refine K s₇ (O.mono (by simp)) ?_ ?_
  · rw [u₇.gpr, u₆.other _ (Ne.symm hlh), u₅.other _ hht, u₄.other _ hht, u₃.other _ hht, eH,
      u₆.other _ (Ne.symm hlt), eT]
    rfl
  · rw [u₇.other _ hlh, u₆.gpr, u₅.other _ hlt, u₄.other _ hlt, u₃.other _ hlt, eL, eT, VG.Proof.Blake2.X86.CompressB.merge,
      BitVec.xor_comm (R.rotateRight k)]

/-- A rotation by `0 < k < 32` of the word in `(l, h)` (low half in `l`) leaves it in `(h, l)`. -/
theorem wp_rot {l h t : Reg} {k : Nat} (h0 : 0 < k) (hk : k < 32) (hlh : l ≠ h) (hlt : l ≠ t)
    (hht : h ≠ t) {x : BitVec 64} (p : Pair s l h x)
    (K : ∀ s', Only [l, h, t] s s' → Pair s' h l (x.rotateRight k) → WP isa (.block rest) s' Q) :
    WP isa (.block (rorPair l h k t ++ rest)) s Q :=
  VG.Proof.Blake2.X86.CompressB.wp_rorPair h0 hk hlh hlt hht p.1 p.2 fun s' o e₁ e₂ => K s' o
    ⟨by rw [e₁, VG.Proof.Blake2.X86.CompressB.merge_eq _ _ h0 hk, lo_rotr x h0 hk], by rw [e₂, VG.Proof.Blake2.X86.CompressB.merge_eq _ _ h0 hk, hi_rotr x h0 hk]⟩

/-- A rotation by `32 + k` (`0 < k < 32`) of the word in `(h, l)` (low half in `h`)
leaves it in `(h, l)`. -/
theorem wp_rot' {l h t : Reg} {k : Nat} (h0 : 0 < k) (hk : k < 32) (hlh : l ≠ h) (hlt : l ≠ t)
    (hht : h ≠ t) {x : BitVec 64} (p : Pair s h l x)
    (K : ∀ s', Only [l, h, t] s s' → Pair s' h l (x.rotateRight (k + 32)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (rorPair l h k t ++ rest)) s Q :=
  VG.Proof.Blake2.X86.CompressB.wp_rorPair h0 hk hlh hlt hht p.2 p.1 fun s' o e₁ e₂ => K s' o
    ⟨by rw [e₁, VG.Proof.Blake2.X86.CompressB.merge_eq _ _ h0 hk, lo_rotr' x (by omega) (by omega), show k + 32 - 32 = k by omega,
        show 64 - (k + 32) = 32 - k by omega],
      by rw [e₂, VG.Proof.Blake2.X86.CompressB.merge_eq _ _ h0 hk, hi_rotr' x (by omega) (by omega), show k + 32 - 32 = k by omega,
        show 64 - (k + 32) = 32 - k by omega]⟩

end

/-! ## `G` -/

/-- The registers `G` writes. -/
def temps : List Reg := [.eax, .ebx, .ecx, .edx, .edi, .ebp]

/-- Two 8-byte words at offsets `o` and `o'` do not overlap. -/
abbrev Sep8 (o o' : Nat) : Prop := o + 8 ≤ o' ∨ o' + 8 ≤ o

theorem Sep8.symm {o o' : Nat} (h : VG.Proof.Blake2.X86.CompressB.Sep8 o o') : VG.Proof.Blake2.X86.CompressB.Sep8 o' o := Or.symm h

/-- `s'` is `s` but for the registers `G` writes, and memory. -/
structure Keep (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.Blake2.X86.CompressB.temps → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (s : State) : VG.Proof.Blake2.X86.CompressB.Keep s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keep.only {s s₁ s₂ : State} {ds : List Reg} (k : VG.Proof.Blake2.X86.CompressB.Keep s s₁) (o : Only ds s₁ s₂)
    (h : ∀ r ∈ ds, r ∈ VG.Proof.Blake2.X86.CompressB.temps) : VG.Proof.Blake2.X86.CompressB.Keep s s₂ :=
  ⟨fun r hr => by rw [o.gpr r (fun hd => hr (h r hd)), k.gpr r hr], o.rd.trans k.rd, o.wr.trans k.wr⟩

theorem Keep.mupd {s s₁ s₂ : State} {m : Mem} (k : VG.Proof.Blake2.X86.CompressB.Keep s s₁) (u : Mupd s₁ s₂ m) : VG.Proof.Blake2.X86.CompressB.Keep s s₂ :=
  ⟨fun r hr => by rw [u.gpr, k.gpr r hr], u.rd.trans k.rd, u.wr.trans k.wr⟩

theorem Keep.trans {s s₁ s₂ : State} (k₁ : VG.Proof.Blake2.X86.CompressB.Keep s s₁) (k₂ : VG.Proof.Blake2.X86.CompressB.Keep s₁ s₂) : VG.Proof.Blake2.X86.CompressB.Keep s s₂ :=
  ⟨fun r hr => by rw [k₂.gpr r hr, k₁.gpr r hr], k₂.rd.trans k₁.rd, k₂.wr.trans k₁.wr⟩

theorem Keep.esi {s s' : State} {B : BitVec 32} (k : VG.Proof.Blake2.X86.CompressB.Keep s s') (h : s.gpr .esi = B) :
    s'.gpr .esi = B := (k.gpr _ (by decide)).trans h

theorem Keep.acc {s s' : State} {B : BitVec 32} {N : Nat} (k : VG.Proof.Blake2.X86.CompressB.Keep s s') (h : Acc s.wr B N) :
    Acc s'.wr B N := k.wr ▸ h

theorem _root_.VG.Proof.Sha512.X86.Pair.mupd {s s' : State} {m : Mem} {l h : Reg} {x : BitVec 64} (p : Pair s l h x)
    (u : Mupd s s' m) : Pair s' l h x :=
  ⟨by rw [u.gpr]; exact p.1, by rw [u.gpr]; exact p.2⟩

/-- The four words `G` computes, from `v[a], v[b], v[c], v[d]` and the message
words `x, y` (`Proof.Blake2.mix` for BLAKE2b). -/
abbrev gOut (va vb vc vd x y : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  Proof.Blake2.mix Spec.Blake2.b va vb vc vd x y

theorem g_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {a b c d x y : Nat}
    (ha : a + 8 ≤ 256) (hb : b + 8 ≤ 256) (hc : c + 8 ≤ 256) (hd : d + 8 ≤ 256)
    (hx : x + 8 ≤ 256) (hy : y + 8 ≤ 256)
    (sab : VG.Proof.Blake2.X86.CompressB.Sep8 a b) (sac : VG.Proof.Blake2.X86.CompressB.Sep8 a c) (sad : VG.Proof.Blake2.X86.CompressB.Sep8 a d) (sbc : VG.Proof.Blake2.X86.CompressB.Sep8 b c) (sbd : VG.Proof.Blake2.X86.CompressB.Sep8 b d)
    (scd : VG.Proof.Blake2.X86.CompressB.Sep8 c d) (syc : VG.Proof.Blake2.X86.CompressB.Sep8 y c) (syd : VG.Proof.Blake2.X86.CompressB.Sep8 y d)
    {s : State} (h0 : s.gpr .esi = B) (hA : Acc s.wr B 512) :
    WP isa (.block (g a b c d x y)) s fun s' => VG.Proof.Blake2.X86.CompressB.Keep s s' ∧
      rd64 s'.mem B a = (VG.Proof.Blake2.X86.CompressB.gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).1 ∧
      rd64 s'.mem B b = (VG.Proof.Blake2.X86.CompressB.gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).2.1 ∧
      rd64 s'.mem B c = (VG.Proof.Blake2.X86.CompressB.gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).2.2.1 ∧
      rd64 s'.mem B d = (VG.Proof.Blake2.X86.CompressB.gOut (rd64 s.mem B a) (rd64 s.mem B b) (rd64 s.mem B c) (rd64 s.mem B d)
        (rd64 s.mem B x) (rd64 s.mem B y)).2.2.2 ∧
      (∀ o, o + 8 ≤ 512 → VG.Proof.Blake2.X86.CompressB.Sep8 a o → VG.Proof.Blake2.X86.CompressB.Sep8 b o → VG.Proof.Blake2.X86.CompressB.Sep8 c o → VG.Proof.Blake2.X86.CompressB.Sep8 d o →
        rd64 s'.mem B o = rd64 s.mem B o) ∧
      Frame [⟨B.setWidth 64, 256⟩] s.mem s'.mem := by
  rw [← List.append_nil (g a b c d x y)]
  unfold g
  simp only [List.append_assoc]
  -- a := a + b + x
  refine wp_ld (by decide) (by decide) h0 hA (by omega) fun s₁ o₁ p₁ => ?_
  have k₁ := (Keep.refl s).only o₁ (by decide)
  refine wp_add64m (by decide) (by decide) (k₁.esi h0) (k₁.acc hA) (by omega) p₁ fun s₂ o₂ p₂ => ?_
  have k₂ := k₁.only o₂ (by decide)
  refine wp_add64m (by decide) (by decide) (k₂.esi h0) (k₂.acc hA) (by omega) p₂ fun s₃ o₃ p₃ => ?_
  have k₃ := k₂.only o₃ (by decide)
  have e₃ : s₂.mem = s.mem := o₂.mem.trans o₁.mem
  rw [o₁.mem, e₃] at p₃
  -- d := (d ^ a) >>> 32
  refine wp_ld (by decide) (by decide) (k₃.esi h0) (k₃.acc hA) (by omega) fun s₄ o₄ p₄ => ?_
  have k₄ := k₃.only o₄ (by decide)
  have e₄ : s₃.mem = s.mem := o₃.mem.trans e₃
  rw [e₄] at p₄
  refine VG.Proof.Blake2.X86.CompressB.wp_xor64 (by decide) (by decide) p₄ (p₃.of_only o₄ (by decide) (by decide))
    fun s₅ o₅ p₅ => ?_
  have k₅ := k₄.only o₅ (by decide)
  have p₅' := p₅.swap
  -- c := c + d
  refine wp_ld (by decide) (by decide) (k₅.esi h0) (k₅.acc hA) (by omega) fun s₆ o₆ p₆ => ?_
  have k₆ := k₅.only o₆ (by decide)
  have e₆ : s₅.mem = s.mem := o₅.mem.trans (o₄.mem.trans e₄)
  rw [e₆] at p₆
  refine wp_add64 (by decide) (by decide) p₆ (p₅'.of_only o₆ (by decide) (by decide))
    fun s₇ o₇ p₇ => ?_
  have k₇ := k₆.only o₇ (by decide)
  refine wp_st (k₇.esi h0) (k₇.acc hA) (by omega) ((p₅'.of_only o₆ (by decide) (by decide)).of_only
    o₇ (by decide) (by decide)) fun s₈ u₈ => ?_
  have k₈ := k₇.mupd u₈
  have e₈ := u₈.mem
  rw [o₇.mem, o₆.mem, e₆] at e₈
  -- b := (b ^ c) >>> 24
  refine wp_ld (by decide) (by decide) (k₈.esi h0) (k₈.acc hA) (by omega) fun s₉ o₉ p₉ => ?_
  have k₉ := k₈.only o₉ (by decide)
  rw [e₈, rd64_write64_ne _ _ (by omega) (by omega) sbd.symm] at p₉
  refine VG.Proof.Blake2.X86.CompressB.wp_xor64 (by decide) (by decide) p₉ ((p₇.mupd u₈).of_only o₉ (by decide) (by decide))
    fun s₁₀ o₁₀ p₁₀ => ?_
  have k₁₀ := k₉.only o₁₀ (by decide)
  refine wp_st (k₁₀.esi h0) (k₁₀.acc hA) (by omega)
    (((p₇.mupd u₈).of_only o₉ (by decide) (by decide)).of_only o₁₀ (by decide) (by decide))
    fun s₁₁ u₁₁ => ?_
  have k₁₁ := k₁₀.mupd u₁₁
  have e₁₁ := u₁₁.mem
  rw [o₁₀.mem, o₉.mem, e₈] at e₁₁
  refine VG.Proof.Blake2.X86.CompressB.wp_rot (by decide) (by decide) (by decide) (by decide) (by decide) (p₁₀.mupd u₁₁)
    fun s₁₂ o₁₂ p₁₂ => ?_
  have k₁₂ := k₁₁.only o₁₂ (by decide)
  -- a := a + b + y
  have pa : Pair s₁₂ .eax .ebx _ :=
    ((((((((p₃.of_only o₄ (by decide) (by decide)).of_only o₅ (by decide) (by decide)).of_only o₆
      (by decide) (by decide)).of_only o₇ (by decide) (by decide)).mupd u₈).of_only o₉ (by decide)
      (by decide)).of_only o₁₀ (by decide) (by decide)).mupd u₁₁).of_only o₁₂ (by decide) (by decide)
  refine wp_add64 (by decide) (by decide) pa p₁₂ fun s₁₃ o₁₃ p₁₃ => ?_
  have k₁₃ := k₁₂.only o₁₃ (by decide)
  refine wp_add64m (by decide) (by decide) (k₁₃.esi h0) (k₁₃.acc hA) (by omega) p₁₃
    fun s₁₄ o₁₄ p₁₄ => ?_
  have k₁₄ := k₁₃.only o₁₄ (by decide)
  have e₁₃ := o₁₃.mem.trans (o₁₂.mem.trans e₁₁)
  rw [e₁₃, rd64_write64_ne _ _ (by omega) (by omega) syc.symm,
    rd64_write64_ne _ _ (by omega) (by omega) syd.symm] at p₁₄
  -- d := (d ^ a) >>> 16
  refine wp_ld (by decide) (by decide) (k₁₄.esi h0) (k₁₄.acc hA) (by omega) fun s₁₅ o₁₅ p₁₅ => ?_
  have k₁₅ := k₁₄.only o₁₅ (by decide)
  rw [o₁₄.mem, e₁₃, rd64_write64_ne _ _ (by omega) (by omega) scd,
    rd64_write64_self _ _ (by omega)] at p₁₅
  refine VG.Proof.Blake2.X86.CompressB.wp_xor64 (by decide) (by decide) p₁₅ (p₁₄.of_only o₁₅ (by decide) (by decide))
    fun s₁₆ o₁₆ p₁₆ => ?_
  have k₁₆ := k₁₅.only o₁₆ (by decide)
  refine wp_st (k₁₆.esi h0) (k₁₆.acc hA) (by omega)
    ((p₁₄.of_only o₁₅ (by decide) (by decide)).of_only o₁₆ (by decide) (by decide))
    fun s₁₇ u₁₇ => ?_
  have k₁₇ := k₁₆.mupd u₁₇
  have e₁₇ := u₁₇.mem
  rw [o₁₆.mem, o₁₅.mem, o₁₄.mem, e₁₃] at e₁₇
  refine VG.Proof.Blake2.X86.CompressB.wp_rot (by decide) (by decide) (by decide) (by decide) (by decide) (p₁₆.mupd u₁₇)
    fun s₁₈ o₁₈ p₁₈ => ?_
  have k₁₈ := k₁₇.only o₁₈ (by decide)
  -- c := c + d
  refine wp_ld (by decide) (by decide) (k₁₈.esi h0) (k₁₈.acc hA) (by omega) fun s₁₉ o₁₉ p₁₉ => ?_
  have k₁₉ := k₁₈.only o₁₉ (by decide)
  rw [o₁₈.mem, e₁₇, rd64_write64_ne _ _ (by omega) (by omega) sac,
    rd64_write64_self _ _ (by omega)] at p₁₉
  refine wp_add64 (by decide) (by decide) p₁₉ (p₁₈.of_only o₁₉ (by decide) (by decide))
    fun s₂₀ o₂₀ p₂₀ => ?_
  have k₂₀ := k₁₉.only o₂₀ (by decide)
  refine wp_st (k₂₀.esi h0) (k₂₀.acc hA) (by omega)
    ((p₁₈.of_only o₁₉ (by decide) (by decide)).of_only o₂₀ (by decide) (by decide))
    fun s₂₁ u₂₁ => ?_
  have k₂₁ := k₂₀.mupd u₂₁
  -- b := (b ^ c) >>> 63
  have pb : Pair s₂₁ .edx .ecx _ :=
    (((((((((p₁₂.of_only o₁₃ (by decide) (by decide)).of_only o₁₄ (by decide) (by decide)).of_only
      o₁₅ (by decide) (by decide)).of_only o₁₆ (by decide) (by decide)).mupd u₁₇).of_only o₁₈
      (by decide) (by decide)).of_only o₁₉ (by decide) (by decide)).of_only o₂₀ (by decide)
      (by decide)).mupd u₂₁)
  refine VG.Proof.Blake2.X86.CompressB.wp_xor64 (by decide) (by decide) pb (p₂₀.mupd u₂₁) fun s₂₂ o₂₂ p₂₂ => ?_
  have k₂₂ := k₂₁.only o₂₂ (by decide)
  refine wp_st (k₂₂.esi h0) (k₂₂.acc hA) (by omega)
    ((p₂₀.mupd u₂₁).of_only o₂₂ (by decide) (by decide)) fun s₂₃ u₂₃ => ?_
  have k₂₃ := k₂₂.mupd u₂₃
  refine VG.Proof.Blake2.X86.CompressB.wp_rot' (by decide) (by decide) (by decide) (by decide) (by decide) (p₂₂.mupd u₂₃)
    fun s₂₄ o₂₄ p₂₄ => ?_
  have k₂₄ := k₂₃.only o₂₄ (by decide)
  refine wp_st (k₂₄.esi h0) (k₂₄.acc hA) (by omega) p₂₄ fun s₂₅ u₂₅ => WP.block_nil ?_
  have k₂₅ := k₂₄.mupd u₂₅
  have e₂₅ := u₂₅.mem
  rw [o₂₄.mem, u₂₃.mem, o₂₂.mem, u₂₁.mem, o₂₀.mem, o₁₉.mem, o₁₈.mem, e₁₇] at e₂₅
  refine ⟨k₂₅, ?_, ?_, ?_, ?_, fun o ho h1 h2 h3 h4 => ?_, ?_⟩
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) sab.symm,
      rd64_write64_ne _ _ (by omega) (by omega) sac.symm,
      rd64_write64_ne _ _ (by omega) (by omega) sad.symm, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) sbc, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) sbd,
      rd64_write64_ne _ _ (by omega) (by omega) scd, rd64_write64_self _ _ (by omega)]
    rfl
  · rw [e₂₅, rd64_write64_ne _ _ (by omega) (by omega) h2,
      rd64_write64_ne _ _ (by omega) (by omega) h3, rd64_write64_ne _ _ (by omega) (by omega) h4,
      rd64_write64_ne _ _ (by omega) (by omega) h1, rd64_write64_ne _ _ (by omega) (by omega) h3,
      rd64_write64_ne _ _ (by omega) (by omega) h4]
  · rw [e₂₅]
    have hm : (⟨B.setWidth 64, 256⟩ : Region) ∈ [(⟨B.setWidth 64, 256⟩ : Region)] :=
      List.mem_singleton_self _
    have f : ∀ {m m' : Mem} {o : Nat} (v : BitVec 64), o + 8 ≤ 256 →
        Frame [⟨B.setWidth 64, 256⟩] m m' → Frame [⟨B.setWidth 64, 256⟩] m (write64 m' B o v) :=
      fun v ho h => frame_write64 h hm (by omega) ho v
    exact f _ hb (f _ hc (f _ hd (f _ ha (f _ hc (f _ hd (Frame.refl _ _))))))

end VG.Proof.Blake2.X86.CompressB

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressB.Body`. -/
section

section

section

/-!
# BLAKE2b on x86 (32-bit): the rounds

`G_step` moves `g_ok` to the work vector (`Holds`), for any four of its words;
`round_ok` composes the eight `G`s of a round, for any round, and `rounds_ok`
the rounds.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86
open VG.Impl.Blake2.X86.CompressB (vOff msgOff g gAt round rounds)
open VG.Proof.Sha512.X86 (Acc rd64)
open VG.Spec.Blake2 (Work Block G)
open VG.Proof.Blake2 (mix G_get)

/-- The work vector `v` is in `scratch[128..256)` (at `B`). -/
def Holds (B : BitVec 32) (v : Work 64) (m : Mem) : Prop :=
  ∀ k (hk : k < 16), rd64 m B (vOff k) = v[k]

/-- The block `M` is in `scratch[0..128)` (at `B`). -/
def Msg (B : BitVec 32) (M : VG.Spec.Blake2.Block 64) (m : Mem) : Prop :=
  ∀ j : Fin 16, rd64 m B (msgOff j) = M j

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : BitVec 32) (M : VG.Spec.Blake2.Block 64) (v : Work 64) (s₀ s : State) : Prop where
  holds : VG.Proof.Blake2.X86.CompressB.Holds B v s.mem
  msg : VG.Proof.Blake2.X86.CompressB.Msg B M s.mem
  keep : VG.Proof.Blake2.X86.CompressB.Keep s₀ s
  frame : Frame [⟨B.setWidth 64, 256⟩] s₀.mem s.mem

theorem vOff_sep {j k : Nat} (_hj : j < 16) (_hk : k < 16) (h : j ≠ k) : VG.Proof.Blake2.X86.CompressB.Sep8 (vOff j) (vOff k) := by
  simp only [VG.Proof.Blake2.X86.CompressB.Sep8, vOff]; omega

theorem msg_vOff (j : Fin 16) {k : Nat} : VG.Proof.Blake2.X86.CompressB.Sep8 (msgOff j) (vOff k) := by
  have := j.2; simp only [VG.Proof.Blake2.X86.CompressB.Sep8, msgOff, vOff]; omega

/-- The side conditions of `G_step`, decidable for concrete arguments: the
four words are distinct. -/
def QSide (a b c d : Nat) : Bool := [a, b, c, d].Nodup

theorem G_step {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {a b c d : Fin 16} (hq : VG.Proof.Blake2.X86.CompressB.QSide a b c d = true)
    {M : VG.Spec.Blake2.Block 64} {v : Work 64} {s : State} (hR : VG.Proof.Blake2.X86.CompressB.RI B M v s₀ s) (j k : Fin 16) :
    WP isa (.block (g (vOff a) (vOff b) (vOff c) (vOff d) (msgOff j) (msgOff k))) s
      (VG.Proof.Blake2.X86.CompressB.RI B M (G Spec.Blake2.b v a b c d (M j) (M k)) s₀) := by
  have nd : (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ a.1 ≠ d.1) ∧ (b.1 ≠ c.1 ∧ b.1 ≠ d.1) ∧ c.1 ≠ d.1 := by
    simpa [VG.Proof.Blake2.X86.CompressB.QSide] using hq
  obtain ⟨⟨nab, nac, nad⟩, ⟨nbc, nbd⟩, ncd⟩ := nd
  have hv : ∀ q : Fin 16, vOff q + 8 ≤ 256 := fun q => by have := q.2; simp only [vOff]; omega
  have hm : ∀ q : Fin 16, msgOff q + 8 ≤ 256 := fun q => by have := q.2; simp only [msgOff]; omega
  refine WP.mono (VG.Proof.Blake2.X86.CompressB.g_ok hfit (hv a) (hv b) (hv c) (hv d) (hm j) (hm k)
    (VG.Proof.Blake2.X86.CompressB.vOff_sep a.2 b.2 nab) (VG.Proof.Blake2.X86.CompressB.vOff_sep a.2 c.2 nac) (VG.Proof.Blake2.X86.CompressB.vOff_sep a.2 d.2 nad) (VG.Proof.Blake2.X86.CompressB.vOff_sep b.2 c.2 nbc)
    (VG.Proof.Blake2.X86.CompressB.vOff_sep b.2 d.2 nbd) (VG.Proof.Blake2.X86.CompressB.vOff_sep c.2 d.2 ncd) (VG.Proof.Blake2.X86.CompressB.msg_vOff k) (VG.Proof.Blake2.X86.CompressB.msg_vOff k)
    (hR.keep.esi h0) (hR.keep.acc hA)) fun s' ⟨hk, ea, eb, ec, ed, other, hf⟩ => ?_
  have ra := hR.holds a a.2
  have rb := hR.holds b b.2
  have rc := hR.holds c c.2
  have rd := hR.holds d d.2
  have rj := hR.msg j
  have rk := hR.msg k
  rw [ra, rb, rc, rd, rj, rk] at ea eb ec ed
  refine ⟨fun q hq => ?_, fun i => ?_, hR.keep.trans hk, hR.frame.trans hf⟩
  · rw [G_get Spec.Blake2.b v nab nac nad nbc nbd ncd _ _ q hq]
    by_cases eqb : b.1 = q
    · subst eqb; simp only [ite_true]; exact eb
    by_cases eqc : c.1 = q
    · subst eqc; simp only [eqb, ite_true, ite_false]; exact ec
    by_cases eqd : d.1 = q
    · subst eqd; simp only [eqb, eqc, ite_true, ite_false]; exact ed
    by_cases eqa : a.1 = q
    · subst eqa; simp only [eqb, eqc, eqd, ite_true, ite_false]; exact ea
    simp only [eqb, eqc, eqd, eqa, ite_false]
    rw [other _ (by simp only [vOff]; omega) (VG.Proof.Blake2.X86.CompressB.vOff_sep a.2 hq eqa) (VG.Proof.Blake2.X86.CompressB.vOff_sep b.2 hq eqb)
      (VG.Proof.Blake2.X86.CompressB.vOff_sep c.2 hq eqc) (VG.Proof.Blake2.X86.CompressB.vOff_sep d.2 hq eqd)]
    exact hR.holds q hq
  · rw [other _ (by have := i.2; simp only [msgOff]; omega) (VG.Proof.Blake2.X86.CompressB.msg_vOff i).symm (VG.Proof.Blake2.X86.CompressB.msg_vOff i).symm
      (VG.Proof.Blake2.X86.CompressB.msg_vOff i).symm (VG.Proof.Blake2.X86.CompressB.msg_vOff i).symm]
    exact hR.msg i

theorem round_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {M : VG.Spec.Blake2.Block 64} {v : Work 64} {s : State}
    (hR : VG.Proof.Blake2.X86.CompressB.RI B M v s₀ s) (r : Nat) :
    WP isa (round r) s (VG.Proof.Blake2.X86.CompressB.RI B M (Spec.Blake2.round Spec.Blake2.b M v r) s₀) := by
  unfold round gAt
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 0) (b := 4) (c := 8) (d := 12) (by decide) hR
    (Spec.Blake2.sigmaAt r 0) (Spec.Blake2.sigmaAt r 1)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 1) (b := 5) (c := 9) (d := 13) (by decide) h₁
    (Spec.Blake2.sigmaAt r 2) (Spec.Blake2.sigmaAt r 3)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 2) (b := 6) (c := 10) (d := 14) (by decide) h₂
    (Spec.Blake2.sigmaAt r 4) (Spec.Blake2.sigmaAt r 5)) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 3) (b := 7) (c := 11) (d := 15) (by decide) h₃
    (Spec.Blake2.sigmaAt r 6) (Spec.Blake2.sigmaAt r 7)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 0) (b := 5) (c := 10) (d := 15) (by decide) h₄
    (Spec.Blake2.sigmaAt r 8) (Spec.Blake2.sigmaAt r 9)) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 1) (b := 6) (c := 11) (d := 12) (by decide) h₅
    (Spec.Blake2.sigmaAt r 10) (Spec.Blake2.sigmaAt r 11)) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 2) (b := 7) (c := 8) (d := 13) (by decide) h₆
    (Spec.Blake2.sigmaAt r 12) (Spec.Blake2.sigmaAt r 13)) fun s₇ h₇ => ?_)
  exact WP.mono (VG.Proof.Blake2.X86.CompressB.G_step hfit h0 hA (a := 3) (b := 4) (c := 9) (d := 14) (by decide) h₇
    (Spec.Blake2.sigmaAt r 14) (Spec.Blake2.sigmaAt r 15)) fun _ h => h

theorem rounds_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {M : VG.Spec.Blake2.Block 64} {v : Work 64}
    (hR : VG.Proof.Blake2.X86.CompressB.RI B M v s₀ s₀) :
    ∀ n, WP isa (rounds n) s₀ (VG.Proof.Blake2.X86.CompressB.RI B M ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.b M) v) s₀)
  | 0 => WP.block_nil hR
  | n + 1 => by
    refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.rounds_ok hfit h0 hA hR n) fun s h => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact VG.Proof.Blake2.X86.CompressB.round_ok hfit h0 hA h n

end VG.Proof.Blake2.X86.CompressB

end

/-!
# BLAKE2b compression function on x86 (32-bit): the precondition

The facts `compressX86 b`'s precondition gives (`Pre`), and the addresses and
regions the code uses.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Block stateAt blockAt)
open VG.Proof.Sha512.X86 (Acc rd64 mem_rd)
open VG.Proof.Sha256.X86.Stream (contains_addr sub_offset)

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
/-- The offset counter of the first block. -/
abbrev t₀ : Nat := (arg s₀ 4 ++ arg s₀ 3).toNat
/-- The final block flag. -/
abbrev fl : Bool := arg s₀ 5 != 0
abbrev scr : BitVec 32 := arg s₀ 6
abbrev stR : Region := ⟨(VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64, 64⟩
abbrev blR : Region := ⟨(VG.Proof.Blake2.X86.CompressB.bp s₀).setWidth 64, 128 * VG.Proof.Blake2.X86.CompressB.nb s₀⟩
abbrev scrR : Region := ⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 512⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(VG.Proof.Blake2.X86.CompressB.esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue 64 := stateAt 64 s₀.mem ((VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Blake2.X86.CompressB.bp s₀ + BitVec.ofNat 32 (128 * i)

/-- Block `i`, as `compressBlocks` reads it. -/
abbrev blk (i : Nat) : VG.Spec.Blake2.Block 64 :=
  blockAt 64 s₀.mem ((VG.Proof.Blake2.X86.CompressB.bp s₀).setWidth 64 + BitVec.ofNat 64 (Spec.Blake2.blockBytes 64 * i))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.X86.CompressB.blR s₀, VG.Proof.Blake2.X86.CompressB.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀]
  st_scr : (VG.Proof.Blake2.X86.CompressB.stR s₀).Disjoint (VG.Proof.Blake2.X86.CompressB.scrR s₀)
  blk_st : (VG.Proof.Blake2.X86.CompressB.blR s₀).Disjoint (VG.Proof.Blake2.X86.CompressB.stR s₀)
  blk_scr : (VG.Proof.Blake2.X86.CompressB.blR s₀).Disjoint (VG.Proof.Blake2.X86.CompressB.scrR s₀)
  arg_st : (VG.Proof.Blake2.X86.CompressB.argR s₀).Disjoint (VG.Proof.Blake2.X86.CompressB.stR s₀)
  arg_scr : (VG.Proof.Blake2.X86.CompressB.argR s₀).Disjoint (VG.Proof.Blake2.X86.CompressB.scrR s₀)
  ret_st : (VG.Proof.Blake2.X86.CompressB.retR s₀).Disjoint (VG.Proof.Blake2.X86.CompressB.stR s₀)
  ret_scr : (VG.Proof.Blake2.X86.CompressB.retR s₀).Disjoint (VG.Proof.Blake2.X86.CompressB.scrR s₀)
  st_fits : (VG.Proof.Blake2.X86.CompressB.st s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Blake2.X86.CompressB.bp s₀).toNat + 128 * VG.Proof.Blake2.X86.CompressB.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Blake2.X86.CompressB.scr s₀).toNat + 512 ≤ 2 ^ 32
  esp_fits : (VG.Proof.Blake2.X86.CompressB.esp₀ s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (VG.Proof.Blake2.compressX86 Spec.Blake2.b).pre s₀) : VG.Proof.Blake2.X86.CompressB.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem addr_ofNat {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    addr x d = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀)
include hp

theorem acc {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (VG.Proof.Blake2.X86.CompressB.scr s₀) 512 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.scr_fits

theorem accS {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (VG.Proof.Blake2.X86.CompressB.st s₀) 64 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.st_fits

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 4 :=
  mem_rd (hp.acc hw d hd)

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 64) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.CompressB.st s₀) d) 4 :=
  mem_rd (hp.accS hw d hd)

theorem argAddr_eq {d : Nat} (hd : d < 32) :
    addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) d = (VG.Proof.Blake2.X86.CompressB.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    (VG.Proof.Blake2.X86.CompressB.argR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) d) 4 := by
  show (⟨addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 4, 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 32) : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Blake2.X86.CompressB.argR s₀, by simp [hrd, hp.rd], hp.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.Blake2.X86.CompressB.argR s₀) := by
  show Region.Sub ⟨addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 4, 28⟩
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀] s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.arg_st.sub_left (hp.arg_sub hi), hp.arg_scr.sub_left (hp.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) :
    (VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i).toNat = (VG.Proof.Blake2.X86.CompressB.bp s₀).toNat + 128 * i := by
  have := hp.blk_fits
  simp only [VG.Proof.Blake2.X86.CompressB.blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) : (VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := hp.blk_fits; rw [hp.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) :
    (VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i).setWidth 64 = (VG.Proof.Blake2.X86.CompressB.bp s₀).setWidth 64 + BitVec.ofNat 64 (128 * i) :=
  addr_eq (x := VG.Proof.Blake2.X86.CompressB.bp s₀) (k := 128 * i) (by have := hp.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) :
    Region.Sub ⟨(VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i).setWidth 64, 128⟩ (VG.Proof.Blake2.X86.CompressB.blR s₀) := by
  have := hp.blk_fits
  rw [hp.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i) o) 4 := by
  refine ⟨VG.Proof.Blake2.X86.CompressB.blR s₀, by simp [hp.rd], ?_⟩
  rw [show addr (VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i) o = addr (VG.Proof.Blake2.X86.CompressB.bp s₀) (128 * i + o) by
    simp only [addr, VG.Proof.Blake2.X86.CompressB.blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact contains_addr (by have : i + 1 ≤ VG.Proof.Blake2.X86.CompressB.nb s₀ := hi; omega) (by omega) hp.blk_fits

theorem blk_disj {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) :
    ∀ r ∈ [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀], Region.Disjoint ⟨(VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i).setWidth 64, 128⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.blk_st.sub_left (hp.blk_sub hi), hp.blk_scr.sub_left (hp.blk_sub hi)⟩

/-- The words of `scratch` from offset 256 on (the parameters and the saved
registers) are unchanged while only `scratch[0, 256)` or the state is written. -/
theorem high_frame {m m' : Mem}
    (hf : Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] m m' ∨ Frame [VG.Proof.Blake2.X86.CompressB.stR s₀] m m') {d : Nat}
    (hd : 256 ≤ d) (hd' : d + 4 ≤ 512) :
    m'.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 := by
  have hc : (⟨addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d, 4⟩ : Region).Contains (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := hp.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left hp.st_scr.symm ?_
    rw [addr_eq (by omega)]
    exact Offset.sub_base _ (by omega)

theorem high_frame64 {m m' : Mem}
    (hf : Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] m m' ∨ Frame [VG.Proof.Blake2.X86.CompressB.stR s₀] m m') {d : Nat}
    (hd : 256 ≤ d) (hd' : d + 8 ≤ 512) :
    rd64 m' (VG.Proof.Blake2.X86.CompressB.scr s₀) d = rd64 m (VG.Proof.Blake2.X86.CompressB.scr s₀) d := by
  simp only [rd64]
  rw [hp.high_frame hf hd (by omega), hp.high_frame hf (by omega) hd']

/-- The state's words are unchanged while only `scratch` is written. -/
theorem st_frame {m m' : Mem} (hf : Frame [VG.Proof.Blake2.X86.CompressB.scrR s₀] m m') {d : Nat} (hd : d + 4 ≤ 64) :
    m'.readW (addr (VG.Proof.Blake2.X86.CompressB.st s₀) d) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressB.st s₀) d) 32 := by
  refine hf.readW (contains_addr (len := 64) hd (by omega) hp.st_fits) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact hp.st_scr

end Pre

end VG.Proof.Blake2.X86.CompressB

end

/-!
# BLAKE2b compression function on x86 (32-bit): the parts of one block

Copying 32-bit words (`copyWords_ok`), which copies the block and the state
into `scratch`; initializing the rest of the work vector (`ivWord_ok`,
`ivXor_ok`); XORing the work vector into the state (`finish_ok`); and
advancing the parameters to the next block (`advance_ok`).
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Work Block stateAt blockAt)
open VG.Proof.Sha512.X86 (Acc rd64 write64 mem_rd readSrc_mem ea_of wp_movS wp_xorS wp_addS
  wp_adcS lo_rd64 hi_rd64 rd64_write64_self rd64_write64_ne)
open VG.Proof.Sha512.Word64 (lo hi readW64 lo_append hi_append hi_append_lo lo_xor hi_xor)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store wp_movi wp_subi
  readW_writeW_addr)

/-! ## 64-bit words in `scratch` -/

section
variable {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32)
include hfit

theorem rw64_ne (m : Mem) (x : BitVec 64) {o o' : Nat} (h : o + 8 ≤ 512) (h' : o' + 8 ≤ 512)
    (hs : VG.Proof.Blake2.X86.CompressB.Sep8 o o') : rd64 (write64 m B o x) B o' = rd64 m B o' :=
  rd64_write64_ne m x (by omega) (by omega) hs

theorem rw64_self (m : Mem) (x : BitVec 64) {o : Nat} (h : o + 8 ≤ 512) :
    rd64 (write64 m B o x) B o = x :=
  rd64_write64_self m x (by omega)

theorem rw32_ne (m : Mem) (x : BitVec 32) {o o' : Nat} (h : o + 4 ≤ 512) (h' : o' + 4 ≤ 512)
    (hs : o + 4 ≤ o' ∨ o' + 4 ≤ o) : (m.writeW (addr B o) x).readW (addr B o') 32 = m.readW (addr B o') 32 :=
  readW_writeW_addr m x (by omega) (by omega) hs.symm

end

/-- A 64-bit word in memory, as its halves. -/
theorem rd64_eq {m : Mem} {x : BitVec 32} {o : Nat} (h : x.toNat + o + 8 ≤ 2 ^ 32) :
    rd64 m x o = m.readW (x.setWidth 64 + BitVec.ofNat 64 o) 64 := by
  rw [readW64, show x.setWidth 64 + BitVec.ofNat 64 o + 4 = x.setWidth 64 + BitVec.ofNat 64 (o + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4, ← addr_eq (by omega), ← addr_eq (by omega)]
  rfl

theorem stateAt_rd64 {x : BitVec 32} (hfit : x.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt 64 m (x.setWidth 64))[k] = rd64 m x (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn]
  rw [VG.Proof.Blake2.X86.CompressB.rd64_eq (by omega)]

/-! ## Copying words -/

/-- Copying `n` words `[src + so + 4j]` to `[esi + d + 4j]`, through `eax`, into
the region `R`, which the words copied are outside of. -/
theorem copyWords_ok {src : Reg} (hsrc : src ≠ .eax) {S D : BitVec 32} {so d n : Nat} {R : Region}
    {s : State} (hS : s.gpr src = S) (hD : s.gpr .esi = D) (hfit : D.toNat + d + 4 * n ≤ 2 ^ 32)
    (hin : ∀ j < n, InRegions (s.rd ++ s.wr) (addr S (so + 4 * j)) 4)
    (hout : ∀ j < n, InRegions s.wr (addr D (d + 4 * j)) 4)
    (hR : ∀ j < n, R.Contains (addr D (d + 4 * j)) 4)
    (hdis : ∀ j < n, Region.Disjoint ⟨addr S (so + 4 * j), 4⟩ R) :
    WP isa (.block (copyWords src so d n)) s fun s' =>
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [R] s.mem s'.mem ∧
      ∀ j < n, s'.mem.readW (addr D (d + 4 * j)) 32 = s.mem.readW (addr S (so + 4 * j)) 32 := by
  unfold copyWords
  refine wp_range_flatMap (M := isa) (fun k (s' : State) => (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [R] s.mem s'.mem ∧
      ∀ j < k, s'.mem.readW (addr D (d + 4 * j)) 32 = s.mem.readW (addr S (so + 4 * j)) 32)
    (fun k s' hk ⟨hg, hrd, hwr, hf, hc⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine wp_movm (ea_of ((hg src hsrc).trans hS) _) (by rw [hrd, hwr]; exact hin k hk)
    fun s₁ u₁ => ?_
  refine wp_store (ea_of (by rw [u₁.other _ (by decide), hg _ (by decide), hD]) _)
    (by rw [u₁.wr, hwr]; exact hout k hk) fun s₂ u₂ => WP.block_nil ?_
  have hv : s'.mem.readW (addr S (so + 4 * k)) 32 = s.mem.readW (addr S (so + 4 * k)) 32 :=
    hf.readW (Region.contains_self _ _) (by simpa using hdis k hk) (by decide)
  refine ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, hg r hr], by rw [u₂.rd, u₁.rd, hrd],
    by rw [u₂.wr, u₁.wr, hwr], ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]; exact hf.writeW (List.mem_singleton_self _) _ (hR k hk)
  · rw [u₂.mem, u₁.gpr, u₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega)]; exact hc j hj
    · rw [Mem.readW_writeW_self32, hv]

/-! ## The rest of the work vector -/

section
variable {rest : List Instr} {Q : State → Prop} {B : BitVec 32} {s : State}

theorem ivWord_ok (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) {k : Nat} (hk : vOff k + 8 ≤ 512)
    (v : BitVec 64)
    (K : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = write64 s.mem B (vOff k) v → WP isa (.block rest) s' Q) :
    WP isa (.block (ivWord k v ++ rest)) s Q := by
  simp only [ivWord, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_store (ea_of (by rw [u₁.other _ (by decide), hD]) _)
    (by rw [u₁.wr]; exact hA _ (by omega)) fun s₂ u₂ => wp_movi fun s₃ u₃ =>
    wp_store (ea_of (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hD]) _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hA _ (by omega)) fun s₄ u₄ => K s₄ ?_ ?_ ?_ ?_
  · intro r hr; rw [u₄.gpr, u₃.other r hr, u₂.gpr, u₁.other r hr]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl

theorem ivXor_ok (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) (hfit : B.toNat + 512 ≤ 2 ^ 32)
    {k o : Nat} (hk : vOff k + 8 ≤ 512) (ho : o + 8 ≤ 512) (hs : VG.Proof.Blake2.X86.CompressB.Sep8 (vOff k) o) (v : BitVec 64)
    (K : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = write64 s.mem B (vOff k) (v ^^^ rd64 s.mem B o) → WP isa (.block rest) s' Q) :
    WP isa (.block (ivXor k v o ++ rest)) s Q := by
  simp only [ivXor, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₁.other _ (by decide), hD])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA _ (by omega)))) fun s₂ u₂ => ?_
  refine wp_store (ea_of (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hD]) _)
    (by rw [u₂.wr, u₁.wr]; exact hA _ (by omega)) fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  have h₄ : s₄.gpr .esi = B := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hD]
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine wp_xorS (readSrc_mem h₄ (by rw [r₄, w₄]; exact mem_rd (hA _ (by omega))))
    fun s₅ u₅ => ?_
  refine wp_store (ea_of (by rw [u₅.other _ (by decide), h₄]) _)
    (by rw [u₅.wr, w₄]; exact hA _ (by omega)) fun s₆ u₆ => K s₆ ?_ ?_ ?_ ?_
  · intro r hr
    rw [u₆.gpr, u₅.other r hr, u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, w₄]
  · rw [u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem,
      readW_writeW_addr _ _ (by omega) (by omega) (by simp only [VG.Proof.Blake2.X86.CompressB.Sep8] at hs; omega)]
    simp only [write64, rd64, lo_xor, hi_xor, lo_append, hi_append]
    rfl

end

/-! ## XORing the work vector into the state -/

/-- After `n` words of `finish`, from the state `s₁`. -/
structure FI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [VG.Proof.Blake2.X86.CompressB.stR s₀] s₁.mem s.mem
  words : ∀ j < 16, s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.st s₀) (4 * j)) 32 =
    if j < n then s₁.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.st s₀) (4 * j)) 32 ^^^
      s₁.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) (vOff 0 + 4 * j)) 32 ^^^
      s₁.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) (vOff 8 + 4 * j)) 32
    else s₁.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.st s₀) (4 * j)) 32

theorem finishWord_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) {s₁ : State} (hc : s₁.gpr .ecx = VG.Proof.Blake2.X86.CompressB.st s₀)
    (he : s₁.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (n : Nat) (hn : n < 16)
    (s : State) (hf : VG.Proof.Blake2.X86.CompressB.FI s₀ s₁ n s) :
    WP isa (.block (finishWord n)) s (VG.Proof.Blake2.X86.CompressB.FI s₀ s₁ (n + 1)) := by
  have fS := hp.st_fits
  have fV := hp.scr_fits
  have hw : s.wr = s₀.wr := hf.wr.trans hwr
  have hsc : s.gpr .ecx = VG.Proof.Blake2.X86.CompressB.st s₀ := (hf.gpr _ (by decide)).trans hc
  have hsi : s.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ := (hf.gpr _ (by decide)).trans he
  -- The scratch words are unchanged.
  have kv : ∀ d, d + 4 ≤ 512 → s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 = s₁.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 :=
    fun d hd => hf.frame.readW (contains_addr (len := 512) hd (by omega) fV)
      (by simpa using hp.st_scr.symm) (by decide)
  simp only [finishWord]
  refine wp_movm (ea_of hsc _) (by rw [hf.rd, hrd, hw]; exact hp.in_st rfl (by omega))
    fun s₂ u₂ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₂.other _ (by decide), hsi])
    (by rw [u₂.rd, u₂.wr, hf.rd, hrd, hw]; exact hp.in_scr rfl (by simp only [vOff]; omega)))
    fun s₃ u₃ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₃.other _ (by decide), u₂.other _ (by decide), hsi])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, hf.rd, hrd, hw]; exact hp.in_scr rfl (by simp only [vOff]; omega)))
    fun s₄ u₄ => ?_
  refine wp_store (ea_of (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), hsc]) _) (by rw [u₄.wr, u₃.wr, u₂.wr, hw]; exact hp.accS rfl _ (by omega))
    fun s₅ u₅ => WP.block_nil ?_
  have hv : s₅.mem = s.mem.writeW (addr (VG.Proof.Blake2.X86.CompressB.st s₀) (4 * n))
      (s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.st s₀) (4 * n)) 32 ^^^ s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) (vOff 0 + 4 * n)) 32 ^^^
        s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) (vOff 8 + 4 * n)) 32) := by
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem]
  refine ⟨fun r hr => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, hf.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, hf.wr], ?_, fun j hj => ?_⟩
  · rw [u₅.gpr, u₄.other r hr, u₃.other r hr, u₂.other r hr, hf.gpr r hr]
  · rw [hv]
    exact hf.frame.writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fS)
  · rw [hv]
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega), hf.words j hj]
      simp only [hjn, show j < n + 1 by omega, ite_true]
    · rcases Nat.eq_or_lt_of_le hjn with rfl | hjn'
      · rw [Mem.readW_writeW_self32, hf.words _ hj, kv _ (by simp only [vOff]; omega),
          kv _ (by simp only [vOff]; omega)]
        simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
      · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega), hf.words j hj]
        simp only [show ¬ j < n by omega, show ¬ j < n + 1 by omega, ite_false]

theorem finishWords_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) {s₁ : State} (hc : s₁.gpr .ecx = VG.Proof.Blake2.X86.CompressB.st s₀)
    (he : s₁.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 16).flatMap finishWord)) s₁ (VG.Proof.Blake2.X86.CompressB.FI s₀ s₁ 16) :=
  wp_range_flatMap (M := isa) (VG.Proof.Blake2.X86.CompressB.FI s₀ s₁) (fun k s hk h => VG.Proof.Blake2.X86.CompressB.finishWord_ok hp hc he hrd hwr k hk s h) 16
    (Nat.le_refl _) s₁ ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j _ => by
      simp only [Nat.not_lt_zero, ite_false]⟩

/-- The state after `finish`, word by word. -/
theorem FI.state {s₀ s₁ s : State} (hf : VG.Proof.Blake2.X86.CompressB.FI s₀ s₁ 16 s) {k : Nat} (hk : k < 8) :
    rd64 s.mem (VG.Proof.Blake2.X86.CompressB.st s₀) (8 * k) = rd64 s₁.mem (VG.Proof.Blake2.X86.CompressB.st s₀) (8 * k) ^^^ rd64 s₁.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) (vOff k) ^^^
      rd64 s₁.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) (vOff (k + 8)) := by
  have e₀ := hf.words (2 * k) (by omega)
  have e₁ := hf.words (2 * k + 1) (by omega)
  rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)] at e₀ e₁
  rw [show vOff 0 + 4 * (2 * k) = vOff k by simp only [vOff]; omega,
    show vOff 8 + 4 * (2 * k) = vOff (k + 8) by simp only [vOff]; omega,
    show 4 * (2 * k) = 8 * k by omega] at e₀
  rw [show vOff 0 + 4 * (2 * k + 1) = vOff k + 4 by simp only [vOff]; omega,
    show vOff 8 + 4 * (2 * k + 1) = vOff (k + 8) + 4 by simp only [vOff]; omega,
    show 4 * (2 * k + 1) = 8 * k + 4 by omega] at e₁
  rw [← hi_append_lo (rd64 s₁.mem (VG.Proof.Blake2.X86.CompressB.st s₀) (8 * k) ^^^ _ ^^^ _), hi_xor, hi_xor, lo_xor, lo_xor,
    hi_rd64, hi_rd64, hi_rd64, lo_rd64, lo_rd64, lo_rd64, ← e₀, ← e₁]
  rfl

/-! ## Advancing to the next block -/

section
variable {rest : List Instr} {Q : State → Prop} {s : State}

theorem wp_movC {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d v → s'.cf = s.cf → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov d src :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := s.setReg d v) (by simp [exec, h])
    (k _ (Upd.setReg _ _ _) rfl)

theorem wp_storeC {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr r)) → s'.cf = s.cf → s'.zf = s.zf →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.store m r :: rest)) s Q := by
  refine Proof.Sha256.X86.Stream.WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)
  simp [exec, State.store32, ha, hout]

theorem wp_adcC {d : Reg} {v : BitVec 32} {c : Bool} (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) →
      s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat + c.toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .adc d (.imm v) :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (by simp [exec, execAlu, readSrc, hc]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addC {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- The parameters after `advance`: the block's address and the 128-bit
counter advanced by 128 bytes, and the count of blocks decremented. -/
def advMem (B : BitVec 32) (m : Mem) : Mem :=
  let T0 := m.readW (addr B tOff) 32
  let T1 := m.readW (addr B (tOff + 4)) 32
  let T2 := m.readW (addr B (tOff + 8)) 32
  let T3 := m.readW (addr B (tOff + 12)) 32
  let c0 := decide (2 ^ 32 ≤ T0.toNat + (128 : BitVec 32).toNat)
  let c1 := decide (2 ^ 32 ≤ T1.toNat + (0 : BitVec 32).toNat + c0.toNat)
  let c2 := decide (2 ^ 32 ≤ T2.toNat + (0 : BitVec 32).toNat + c1.toNat)
  ((((((m.writeW (addr B blOff) (m.readW (addr B blOff) 32 + 128)).writeW (addr B tOff)
    (T0 + 128)).writeW (addr B (tOff + 4)) (T1 + 0 + (BitVec.ofBool c0).setWidth 32)).writeW
    (addr B (tOff + 8)) (T2 + 0 + (BitVec.ofBool c1).setWidth 32)).writeW (addr B (tOff + 12))
    (T3 + 0 + (BitVec.ofBool c2).setWidth 32)).writeW (addr B nOff) (m.readW (addr B nOff) 32 - 1))

theorem advance_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s : State}
    (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) :
    WP isa (.block advance) s fun s' =>
      s'.mem = VG.Proof.Blake2.X86.CompressB.advMem B s.mem ∧ s'.zf = some (s.mem.readW (addr B nOff) 32 - 1 == 0) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r32 := VG.Proof.Blake2.X86.CompressB.rw32_ne hfit
  have inr : ∀ (rs : List Region) (o : Nat), o + 4 ≤ 512 → InRegions (rs ++ s.wr) (addr B o) 4 :=
    fun rs o ho => let ⟨r, hr, hc⟩ := hA o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  unfold advance
  -- The block's address.
  refine wp_movm (ea_of hD _) (mem_rd (hA blOff (by decide))) fun s₁ u₁ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_addC fun s₂ u₂ _ => ?_
  have e₂ : s₂.gpr .esi = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hD]
  have w₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  refine VG.Proof.Blake2.X86.CompressB.wp_storeC (ea_of e₂ _) (by rw [w₂]; exact hA blOff (by decide)) fun s₃ u₃ _ _ => ?_
  -- The counter.
  refine wp_movm (ea_of (by rw [u₃.gpr, e₂]) _) (by rw [u₃.wr, w₂]; exact inr _ tOff (by decide))
    fun s₄ u₄ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_addC fun s₅ u₅ c₅ => ?_
  have e₅ : s₅.gpr .esi = B := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e₂]
  have w₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, w₂]
  refine VG.Proof.Blake2.X86.CompressB.wp_storeC (ea_of e₅ _) (by rw [w₅]; exact hA tOff (by decide)) fun s₆ u₆ f₆ _ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_movC (readSrc_mem (by rw [u₆.gpr, e₅]) (by rw [u₆.wr, w₅]; exact inr _ (tOff + 4) (by decide)))
    fun s₇ u₇ f₇ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_adcC (f₇.trans (f₆.trans c₅)) fun s₈ u₈ c₈ => ?_
  have e₈ : s₈.gpr .esi = B := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e₅]
  have w₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, w₅]
  refine VG.Proof.Blake2.X86.CompressB.wp_storeC (ea_of e₈ _) (by rw [w₈]; exact hA (tOff + 4) (by decide)) fun s₉ u₉ f₉ _ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_movC (readSrc_mem (by rw [u₉.gpr, e₈]) (by rw [u₉.wr, w₈]; exact inr _ (tOff + 8) (by decide)))
    fun s₁₀ u₁₀ f₁₀ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_adcC (f₁₀.trans (f₉.trans c₈)) fun s₁₁ u₁₁ c₁₁ => ?_
  have e₁₁ : s₁₁.gpr .esi = B := by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, e₈]
  have w₁₁ : s₁₁.wr = s.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, w₈]
  refine VG.Proof.Blake2.X86.CompressB.wp_storeC (ea_of e₁₁ _) (by rw [w₁₁]; exact hA (tOff + 8) (by decide)) fun s₁₂ u₁₂ f₁₂ _ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_movC (readSrc_mem (by rw [u₁₂.gpr, e₁₁]) (by rw [u₁₂.wr, w₁₁]; exact inr _ (tOff + 12) (by decide)))
    fun s₁₃ u₁₃ f₁₃ => ?_
  refine VG.Proof.Blake2.X86.CompressB.wp_adcC (f₁₃.trans (f₁₂.trans c₁₁)) fun s₁₄ u₁₄ _ => ?_
  have e₁₄ : s₁₄.gpr .esi = B := by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, e₁₁]
  have w₁₄ : s₁₄.wr = s.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, w₁₁]
  refine VG.Proof.Blake2.X86.CompressB.wp_storeC (ea_of e₁₄ _) (by rw [w₁₄]; exact hA (tOff + 12) (by decide)) fun s₁₅ u₁₅ _ _ => ?_
  -- The count.
  refine wp_movm (ea_of (by rw [u₁₅.gpr, e₁₄]) _)
    (by rw [u₁₅.wr, w₁₄]; exact inr _ nOff (by decide)) fun s₁₆ u₁₆ => ?_
  refine wp_subi fun s₁₇ u₁₇ z₁₇ => ?_
  have e₁₇ : s₁₇.gpr .esi = B := by rw [u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₅.gpr, e₁₄]
  have w₁₇ : s₁₇.wr = s.wr := by rw [u₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄]
  refine VG.Proof.Blake2.X86.CompressB.wp_storeC (ea_of e₁₇ _) (by rw [w₁₇]; exact hA nOff (by decide)) fun s₁₈ u₁₈ _ z₁₈ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · simp (disch := decide) only [VG.Proof.Blake2.X86.CompressB.advMem, u₁₈.mem, u₁₇.gpr, u₁₇.mem, u₁₆.gpr, u₁₆.mem,
      u₁₅.mem, u₁₄.gpr, u₁₄.mem, u₁₃.gpr, u₁₃.mem, u₁₂.mem, u₁₁.gpr, u₁₁.mem,
      u₁₀.gpr, u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, u₇.gpr, u₇.mem, u₆.mem, u₅.gpr,
      u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, r32]
  · rw [z₁₈, z₁₇]
    simp (disch := decide) only [u₁₆.gpr, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem,
      u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, r32]
  · rw [u₁₈.gpr, u₁₇.other r hr, u₁₆.other r hr, u₁₅.gpr, u₁₄.other r hr, u₁₃.other r hr, u₁₂.gpr,
      u₁₁.other r hr, u₁₀.other r hr, u₉.gpr, u₈.other r hr, u₇.other r hr, u₆.gpr, u₅.other r hr,
      u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd,
      u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₈.wr, w₁₇]

end VG.Proof.Blake2.X86.CompressB

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressB.Compress`. -/
section

/-!
# BLAKE2b compression function on x86 (32-bit): one block and the loop

`body_ok`: one block, from the invariant `Common` after `i` blocks to `Common`
after `i + 1`; `correct`: the whole function.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Work Block stateAt blockAt compressBlocks)
open VG.Proof.Sha512.X86 (Acc rd64 write64 mem_rd readSrc_mem ea_of lo_rd64 hi_rd64 rd64_frame)
open VG.Proof.Sha512.Word64 (lo hi readW64 lo_append hi_append hi_append_lo)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store readW_writeW_addr)

/-! ## Regions within the 32-bit address space -/

theorem addr_contains {x : BitVec 32} {d n e k : Nat} (hfit : x.toNat + e + k ≤ 2 ^ 32)
    (hn : 0 < n) (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) : (⟨addr x e, k⟩ : Region).Contains (addr x d) n := by
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ h₁ h₂ (by omega)

theorem addr_sub {x : BitVec 32} {d n k : Nat} (h : d + n ≤ k) (hfit : x.toNat + k ≤ 2 ^ 32) :
    Region.Sub ⟨addr x d, n⟩ ⟨x.setWidth 64, k⟩ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · intro a ha; simp [Region.Contains] at ha
  rw [addr_eq (by omega)]
  exact Offset.sub_base _ h

theorem Region.Sub.trans' {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) :
    Region.Sub a c := fun x h => h₂ x (h₁ x h)

/-! ## The compression function, in the order of the code -/

/-- The final block flag as a word. -/
def flagW (f : Bool) : BitVec 64 := if f then BitVec.allOnes 64 else 0

/-- The work vector before the rounds (RFC 7693 §3.2). -/
def V0 (h : HashValue 64) (t : Nat) (f : Bool) : Work 64 :=
  let v : Work 64 := h ++ Spec.Blake2.b.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat 64 t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat 64 (t / 2 ^ 64))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 64) else v

theorem F_eq (h : HashValue 64) (m : VG.Spec.Blake2.Block 64) (t : Nat) (f : Bool) :
    Spec.Blake2.F Spec.Blake2.b h m t f = Vector.ofFn fun i : Fin 8 =>
      (h[i]'(by omega)) ^^^ ((List.range 12).foldl (Spec.Blake2.round Spec.Blake2.b m) (VG.Proof.Blake2.X86.CompressB.V0 h t f))[i] ^^^
        ((List.range 12).foldl (Spec.Blake2.round Spec.Blake2.b m) (VG.Proof.Blake2.X86.CompressB.V0 h t f))[i.val + 8] := rfl

theorem V0_get (h : HashValue 64) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) :
    (VG.Proof.Blake2.X86.CompressB.V0 h t f)[k] =
      if hk8 : k < 8 then (h[k]'(by omega)) else if k = 12 then Spec.Blake2.b.IV[4] ^^^ BitVec.ofNat 64 t
      else if k = 13 then Spec.Blake2.b.IV[5] ^^^ BitVec.ofNat 64 (t / 2 ^ 64)
      else if k = 14 then Spec.Blake2.b.IV[6] ^^^ VG.Proof.Blake2.X86.CompressB.flagW f else Spec.Blake2.b.IV[k - 8]'(by omega) := by
  have base : ((h ++ Spec.Blake2.b.IV : Work 64))[k] =
      if hk8 : k < 8 then (h[k]'(by omega)) else Spec.Blake2.b.IV[k - 8]'(by omega) := by
    simp only [Vector.getElem_append]
  have e12 : (h ++ Spec.Blake2.b.IV : Work 64)[12] = Spec.Blake2.b.IV[4] := by
    simp only [Vector.getElem_append]; rfl
  have e13 : (h ++ Spec.Blake2.b.IV : Work 64)[13] = Spec.Blake2.b.IV[5] := by
    simp only [Vector.getElem_append]; rfl
  have e14 : (h ++ Spec.Blake2.b.IV : Work 64)[14] = Spec.Blake2.b.IV[6] := by
    simp only [Vector.getElem_append]; rfl
  by_cases k14 : k = 14
  · subst k14; cases f <;> simp [VG.Proof.Blake2.X86.CompressB.V0, VG.Proof.Blake2.X86.CompressB.flagW, e14]
  by_cases k13 : k = 13
  · subst k13; cases f <;> simp [VG.Proof.Blake2.X86.CompressB.V0, e13]
  by_cases k12 : k = 12
  · subst k12; cases f <;> simp [VG.Proof.Blake2.X86.CompressB.V0, e12]
  have n14 : ¬14 = k := Ne.symm k14
  have n13 : ¬13 = k := Ne.symm k13
  have n12 : ¬12 = k := Ne.symm k12
  cases f <;> simp only [VG.Proof.Blake2.X86.CompressB.V0, Vector.getElem_set, n14, n13, n12, k14, k13, k12, ite_false, base,
    Bool.false_eq_true, ite_true]

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in `scratch`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (VG.Proof.Blake2.X86.CompressB.scr s₀)) s₀.gpr saved

theorem saved_fits : Spill.Fits 304 saved := by decide

theorem saved_bounds : ∀ p ∈ saved, 288 ≤ p.2 ∧ p.2 + 4 ≤ 512 := by decide

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀
  esp : s.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀] s₀.mem s.mem
  state : stateAt 64 s.mem ((VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64) =
    compressBlocks Spec.Blake2.b (VG.Proof.Blake2.X86.CompressB.H₀ s₀) s₀.mem ((VG.Proof.Blake2.X86.CompressB.bp s₀).setWidth 64) i (VG.Proof.Blake2.X86.CompressB.t₀ s₀) (VG.Proof.Blake2.X86.CompressB.fl s₀)
  saved : VG.Proof.Blake2.X86.CompressB.Saved s₀ s.mem
  bl : s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) blOff) 32 = VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i
  n : s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) nOff) 32 = BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressB.nb s₀ - i)
  tlo : rd64 s.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) tOff = BitVec.ofNat 64 (VG.Proof.Blake2.X86.CompressB.t₀ s₀ + i * Spec.Blake2.blockBytes 64)
  thi : rd64 s.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) (tOff + 8) =
    BitVec.ofNat 64 ((VG.Proof.Blake2.X86.CompressB.t₀ s₀ + i * Spec.Blake2.blockBytes 64) / 2 ^ 64)
  f : rd64 s.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) fOff = VG.Proof.Blake2.X86.CompressB.flagW (VG.Proof.Blake2.X86.CompressB.fl s₀)

/-! ## Copies of 32-bit words as 64-bit words -/

theorem rd64_of_copy {m m' : Mem} {D S : BitVec 32} {d so n : Nat}
    (h : ∀ j < n, m'.readW (addr D (d + 4 * j)) 32 = m.readW (addr S (so + 4 * j)) 32) {k : Nat}
    (hk : 2 * k + 1 < n) {d' so' : Nat} (hd : d' = d + 8 * k) (hs : so' = so + 8 * k) :
    rd64 m' D d' = rd64 m S so' := by
  have e₀ := h (2 * k) (by omega)
  have e₁ := h (2 * k + 1) (by omega)
  rw [show d + 4 * (2 * k) = d' by omega, show so + 4 * (2 * k) = so' by omega] at e₀
  rw [show d + 4 * (2 * k + 1) = d' + 4 by omega, show so + 4 * (2 * k + 1) = so' + 4 by omega] at e₁
  simp only [rd64]; rw [e₀, e₁]

theorem blk_rd64 {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) (j : Fin 16) :
    VG.Proof.Blake2.X86.CompressB.blk s₀ i j = rd64 s₀.mem (VG.Proof.Blake2.X86.CompressB.blkAddr s₀ i) (8 * j) := by
  have := hp.blk_fit hi
  have hj := j.2
  rw [VG.Proof.Blake2.X86.CompressB.rd64_eq (by omega), hp.blk_addr hi]
  exact Proof.Blake2.blockAt_word _ _ _ hj

/-! ## Copying the block and initializing the work vector -/

theorem stage1_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) {s : State}
    (hc : VG.Proof.Blake2.X86.CompressB.Common s₀ i s) :
    WP isa (.block (copy ++ VG.Impl.Blake2.X86.CompressB.init)) s fun s' =>
      VG.Proof.Blake2.X86.CompressB.RI (VG.Proof.Blake2.X86.CompressB.scr s₀) (VG.Proof.Blake2.X86.CompressB.blk s₀ i)
        (VG.Proof.Blake2.X86.CompressB.V0 (stateAt 64 s.mem ((VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64)) (VG.Proof.Blake2.X86.CompressB.t₀ s₀ + i * Spec.Blake2.blockBytes 64)
          (VG.Proof.Blake2.X86.CompressB.fl s₀)) s' s' ∧
      Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] s.mem s'.mem ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ ∧ s'.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀ := by
  have fV := hp.scr_fits
  have fS := hp.st_fits
  have fB := hp.blk_fit hi
  have hm₁ : (⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 128⟩ : Region) ∈ [(⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 128⟩ : Region)] :=
    List.mem_singleton_self _
  rw [WP.block_append_iff]
  -- The block.
  unfold copy
  refine wp_movm (ea_of hc.esi _) (hp.in_scr hc.wr (by decide)) fun s₁ u₁ => ?_
  rw [hc.bl] at u₁
  refine WP.mono (VG.Proof.Blake2.X86.CompressB.copyWords_ok (src := .edi) (R := ⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 128⟩) (by decide) u₁.gpr
    (by rw [u₁.other _ (by decide), hc.esi]) (by omega)
    (fun j hj => by rw [u₁.rd, u₁.wr, hc.rd, hc.wr]; exact hp.blk_rd hi (by omega))
    (fun j hj => by rw [u₁.wr, hc.wr]; exact hp.acc rfl _ (by omega))
    (fun j hj => contains_addr (by omega) (by omega) (by omega))
    (fun j hj => (hp.blk_scr.sub_left (Region.Sub.trans' (VG.Proof.Blake2.X86.CompressB.addr_sub (by omega) fB)
      (hp.blk_sub hi))).sub_right (Region.sub_prefix (by omega))))
    fun s₂ ⟨g₂, rd₂, wr₂, f₂, c₂⟩ => ?_
  have hmsg₂ : VG.Proof.Blake2.X86.CompressB.Msg (VG.Proof.Blake2.X86.CompressB.scr s₀) (VG.Proof.Blake2.X86.CompressB.blk s₀ i) s₂.mem := fun j => by
    have hj := j.2
    rw [VG.Proof.Blake2.X86.CompressB.blk_rd64 hp hi j, VG.Proof.Blake2.X86.CompressB.rd64_of_copy c₂ (k := j) (by omega) (by simp only [msgOff]; omega) rfl,
      u₁.mem, Nat.zero_add]
    exact rd64_frame hc.frame (hp.blk_disj hi) fB (by omega)
  have F₂ : Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] s.mem s₂.mem := by
    rw [← u₁.mem]
    exact f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hrd₂ : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd, hc.rd]
  have hwr₂ : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr, hc.wr]
  have hesi₂ : s₂.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), hc.esi]
  have hesp₂ : s₂.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), hc.esp]
  have hF₂ : Frame [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀] s₀.mem s₂.mem :=
    hc.frame.trans (F₂.sub fun r hr => ⟨VG.Proof.Blake2.X86.CompressB.scrR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)
  -- The state.
  unfold VG.Impl.Blake2.X86.CompressB.init
  refine wp_movm (ea_of hesp₂ _) (hp.in_arg hrd₂ (by decide) (by decide)) fun s₃ u₃ => ?_
  have ecx₃ : s₃.gpr .ecx = VG.Proof.Blake2.X86.CompressB.st s₀ := by rw [u₃.gpr]; exact hp.arg_frame hF₂ (i := 0) (by decide)
  rw [List.append_eq, WP.block_append_iff]
  have hR₃ : ∀ j < 16, (⟨addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 128, 128⟩ : Region).Contains (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) (vOff 0 + 4 * j)) 4 :=
    fun j hj => VG.Proof.Blake2.X86.CompressB.addr_contains (by omega) (by decide) (by simp only [vOff]; omega)
      (by simp only [vOff]; omega)
  refine WP.mono (VG.Proof.Blake2.X86.CompressB.copyWords_ok (src := .ecx) (S := VG.Proof.Blake2.X86.CompressB.st s₀) (D := VG.Proof.Blake2.X86.CompressB.scr s₀) (so := 0) (d := vOff 0)
    (n := 16) (R := ⟨addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 128, 128⟩) (by decide) ecx₃ (by rw [u₃.other _ (by decide), hesi₂])
    (by simp only [vOff]; omega)
    (fun j hj => by rw [u₃.rd, u₃.wr]; exact hp.in_st hwr₂ (by omega))
    (fun j hj => by rw [u₃.wr, hwr₂]; exact hp.acc rfl _ (by simp only [vOff]; omega)) hR₃
    (fun j hj => (hp.st_scr.sub_left (VG.Proof.Blake2.X86.CompressB.addr_sub (by omega) fS)).sub_right
      (Region.Sub.trans' (VG.Proof.Blake2.X86.CompressB.addr_sub (by omega) fV) (Region.sub_prefix (Nat.le_refl _)))))
    fun s₄ ⟨g₄, rd₄, wr₄, f₄, c₄⟩ => ?_
  have hesi₄ : s₄.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ := by rw [g₄ _ (by decide), u₃.other _ (by decide), hesi₂]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, u₃.wr, hwr₂]
  have hA := hp.acc hwr₄
  -- The rest of the work vector.
  rw [← List.append_nil (ivWord 15 _)]
  refine VG.Proof.Blake2.X86.CompressB.ivWord_ok hesi₄ hA (by decide) _ fun s₅ g₅ rd₅ wr₅ m₅ => ?_
  refine VG.Proof.Blake2.X86.CompressB.ivWord_ok (by rw [g₅ _ (by decide), hesi₄]) (by rw [wr₅]; exact hA) (by decide) _
    fun s₆ g₆ rd₆ wr₆ m₆ => ?_
  refine VG.Proof.Blake2.X86.CompressB.ivWord_ok (by rw [g₆ _ (by decide), g₅ _ (by decide), hesi₄]) (by rw [wr₆, wr₅]; exact hA)
    (by decide) _ fun s₇ g₇ rd₇ wr₇ m₇ => ?_
  refine VG.Proof.Blake2.X86.CompressB.ivWord_ok (by rw [g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), hesi₄])
    (by rw [wr₇, wr₆, wr₅]; exact hA) (by decide) _ fun s₈ g₈ rd₈ wr₈ m₈ => ?_
  have e₈ : s₈.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ := by
    rw [g₈ _ (by decide), g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), hesi₄]
  have w₈ : s₈.wr = s₄.wr := by rw [wr₈, wr₇, wr₆, wr₅]
  refine VG.Proof.Blake2.X86.CompressB.ivXor_ok e₈ (by rw [w₈]; exact hA) fV (by decide) (by decide) (by decide) _
    fun s₉ g₉ rd₉ wr₉ m₉ => ?_
  refine VG.Proof.Blake2.X86.CompressB.ivXor_ok (by rw [g₉ _ (by decide), e₈]) (by rw [wr₉, w₈]; exact hA) fV (by decide)
    (by decide) (by decide) _ fun s₁₀ g₁₀ rd₁₀ wr₁₀ m₁₀ => ?_
  refine VG.Proof.Blake2.X86.CompressB.ivXor_ok (by rw [g₁₀ _ (by decide), g₉ _ (by decide), e₈]) (by rw [wr₁₀, wr₉, w₈]; exact hA)
    fV (by decide) (by decide) (by decide) _ fun s₁₁ g₁₁ rd₁₁ wr₁₁ m₁₁ => ?_
  refine VG.Proof.Blake2.X86.CompressB.ivWord_ok (by rw [g₁₁ _ (by decide), g₁₀ _ (by decide), g₉ _ (by decide), e₈])
    (by rw [wr₁₁, wr₁₀, wr₉, w₈]; exact hA) (by decide) _
    fun s₁₂ g₁₂ rd₁₂ wr₁₂ m₁₂ => WP.block_nil ?_
  -- Frames.
  have hm : (⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩ : Region) ∈ [(⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩ : Region)] :=
    List.mem_singleton_self _
  have fw : ∀ {m m' : Mem} {o : Nat} (v : BitVec 64), o + 8 ≤ 256 →
      Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] m m' →
      Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] m (write64 m' (VG.Proof.Blake2.X86.CompressB.scr s₀) o v) :=
    fun v ho h => Proof.Sha512.X86.frame_write64 h hm (by omega) ho v
  have F₄ : Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] s.mem s₄.mem := by
    refine F₂.trans ?_
    rw [← u₃.mem]
    exact f₄.sub fun r hr => ⟨_, hm, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.Blake2.X86.CompressB.addr_sub (by omega) (by omega)⟩
  have F₁₂ : Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] s.mem s₁₂.mem := by
    rw [m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆, m₅]
    exact fw _ (by decide) (fw _ (by decide) (fw _ (by decide) (fw _ (by decide) (fw _ (by decide)
      (fw _ (by decide) (fw _ (by decide) (fw _ (by decide) F₄)))))))
  -- The parameters, read through the copies.
  have hi₄ : ∀ d, 256 ≤ d → d + 8 ≤ 512 → rd64 s₄.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) d = rd64 s.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) d :=
    fun d h1 h2 => hp.high_frame64 (.inl F₄) h1 h2
  have tl₄ := (hi₄ tOff (by decide) (by decide)).trans hc.tlo
  have th₄ := (hi₄ (tOff + 8) (by decide) (by decide)).trans hc.thi
  have fl₄ := (hi₄ fOff (by decide) (by decide)).trans hc.f
  have r₅ := VG.Proof.Blake2.X86.CompressB.rw64_ne fV; have r₆ := VG.Proof.Blake2.X86.CompressB.rw64_self fV
  -- The work vector.
  have hold : VG.Proof.Blake2.X86.CompressB.Holds (VG.Proof.Blake2.X86.CompressB.scr s₀)
      (VG.Proof.Blake2.X86.CompressB.V0 (stateAt 64 s.mem ((VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64)) (VG.Proof.Blake2.X86.CompressB.t₀ s₀ + i * Spec.Blake2.blockBytes 64)
        (VG.Proof.Blake2.X86.CompressB.fl s₀)) s₁₂.mem := by
    intro k hk
    rw [VG.Proof.Blake2.X86.CompressB.V0_get _ _ _ k hk]
    by_cases hk8 : k < 8
    · simp only [hk8, dite_true]
      have sp : ∀ j, 8 ≤ j → j < 16 → VG.Proof.Blake2.X86.CompressB.Sep8 (vOff j) (vOff k) := fun j h1 h2 => by
        simp only [VG.Proof.Blake2.X86.CompressB.Sep8, vOff]; omega
      have vk : vOff k + 8 ≤ 512 := by simp only [vOff]; omega
      rw [m₁₂, r₅ _ _ (by decide) vk (sp 15 (by decide) (by decide)), m₁₁,
        r₅ _ _ (by decide) vk (sp 14 (by decide) (by decide)), m₁₀,
        r₅ _ _ (by decide) vk (sp 13 (by decide) (by decide)), m₉,
        r₅ _ _ (by decide) vk (sp 12 (by decide) (by decide)), m₈,
        r₅ _ _ (by decide) vk (sp 11 (by decide) (by decide)), m₇,
        r₅ _ _ (by decide) vk (sp 10 (by decide) (by decide)), m₆,
        r₅ _ _ (by decide) vk (sp 9 (by decide) (by decide)), m₅,
        r₅ _ _ (by decide) vk (sp 8 (by decide) (by decide)),
        VG.Proof.Blake2.X86.CompressB.rd64_of_copy c₄ (k := k) (by omega) (by unfold vOff; omega) rfl, u₃.mem, Nat.zero_add,
        VG.Proof.Blake2.X86.CompressB.stateAt_rd64 fS _ hk8]
      exact rd64_frame F₂ (by simpa using hp.st_scr.sub_right (Region.sub_prefix (by omega))) fS
        (by omega)
    · -- The eight words at once, so that `simp` shares its work on the writes.
      have hk' : k ∈ ([8, 9, 10, 11, 12, 13, 14, 15] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
      revert hk hk8
      revert hk'
      revert k
      simp (disch := decide) only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, not_false_eq_true, imp_self, and_self,
        m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆, m₅, r₅, r₆, tl₄, th₄, fl₄,
        dite_false, ite_true, ite_false, Nat.reduceSub, Nat.lt_irrefl, Nat.reduceLT,
        Nat.reduceEqDiff]
  have hmsg : VG.Proof.Blake2.X86.CompressB.Msg (VG.Proof.Blake2.X86.CompressB.scr s₀) (VG.Proof.Blake2.X86.CompressB.blk s₀ i) s₁₂.mem := fun j => by
    have hj := j.2
    have mj : msgOff j + 8 ≤ 512 := by simp only [msgOff]; omega
    have sp : ∀ k, VG.Proof.Blake2.X86.CompressB.Sep8 (vOff k) (msgOff j) := fun k => (VG.Proof.Blake2.X86.CompressB.msg_vOff j).symm
    rw [m₁₂, r₅ _ _ (by decide) mj (sp _), m₁₁, r₅ _ _ (by decide) mj (sp _), m₁₀,
      r₅ _ _ (by decide) mj (sp _), m₉, r₅ _ _ (by decide) mj (sp _), m₈,
      r₅ _ _ (by decide) mj (sp _), m₇, r₅ _ _ (by decide) mj (sp _), m₆,
      r₅ _ _ (by decide) mj (sp _), m₅, r₅ _ _ (by decide) mj (sp _),
      rd64_frame f₄ (N := 128) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [addr_eq (by omega)]; exact Offset.base_disjoint _ (by decide) (by decide))
        (by omega) (by simp only [msgOff]; omega), u₃.mem]
    exact hmsg₂ j
  refine ⟨⟨hold, hmsg, Keep.refl _, Frame.refl _ _⟩, F₁₂, ?_, ?_, ?_, ?_⟩
  · rw [rd₁₂, rd₁₁, rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, rd₄, u₃.rd, hrd₂]
  · rw [wr₁₂, wr₁₁, wr₁₀, wr₉, w₈, hwr₄]
  · rw [g₁₂ _ (by decide), g₁₁ _ (by decide), g₁₀ _ (by decide), g₉ _ (by decide), e₈]
  · rw [g₁₂ _ (by decide), g₁₁ _ (by decide), g₁₀ _ (by decide), g₉ _ (by decide),
      g₈ _ (by decide), g₇ _ (by decide), g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide),
      u₃.other _ (by decide), hesp₂]

/-! ## The parameters after `advance` -/

theorem advMem_frame {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) (m : Mem) : Frame [VG.Proof.Blake2.X86.CompressB.scrR s₀] m (VG.Proof.Blake2.X86.CompressB.advMem (VG.Proof.Blake2.X86.CompressB.scr s₀) m) := by
  have c : ∀ d, d + 4 ≤ 512 → (VG.Proof.Blake2.X86.CompressB.scrR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) (32 / 8) :=
    fun d hd => contains_addr hd (by omega) hp.scr_fits
  have hm := List.mem_singleton_self (VG.Proof.Blake2.X86.CompressB.scrR s₀)
  simp only [VG.Proof.Blake2.X86.CompressB.advMem]
  exact ((((((Frame.refl _ _).writeW hm _ (c _ (by decide))).writeW hm _ (c _ (by decide))).writeW
    hm _ (c _ (by decide))).writeW hm _ (c _ (by decide))).writeW hm _ (c _ (by decide))).writeW hm _
    (c _ (by decide))

/-- A 64-bit addition of a 32-bit constant, by `add` and `adc` of the halves. -/
theorem add_halves (L H : BitVec 32) (y : BitVec 32) :
    (H + 0 + (BitVec.ofBool (decide (2 ^ 32 ≤ L.toNat + y.toNat))).setWidth 32) ++ (L + y) =
      (H ++ L) + y.setWidth 64 := by
  apply Proof.Sha512.Word64.eq_of_lo_hi
  · rw [lo_append, Proof.Sha512.Word64.lo_add, lo_append]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [lo]
    exact (Nat.mod_eq_of_lt y.isLt).symm
  · rw [hi_append, Proof.Sha512.Word64.hi_add, hi_append, lo_append, Proof.Sha512.X86.carry_eq]
    have e1 : hi (y.setWidth 64) = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [Proof.Sha512.Word64.hi_toNat]; simp; omega
    have e2 : (lo (y.setWidth 64)).toNat = y.toNat := by
      rw [Proof.Sha512.Word64.lo_toNat]; simp; exact y.isLt
    rw [e1, e2]

/-- The carry out of `add_halves`. -/
theorem carry_halves (L H : BitVec 32) (y : BitVec 32) :
    (2 ^ 32 ≤ H.toNat + (0 : BitVec 32).toNat +
      (decide (2 ^ 32 ≤ L.toNat + y.toNat)).toNat) ↔ 2 ^ 64 ≤ (H ++ L).toNat + y.toNat := by
  have hL := L.isLt; have hH := H.isLt; have hy := y.isLt
  have e : (H ++ L).toNat = H.toNat * 2 ^ 32 + L.toNat := by
    have := Proof.Sha512.Word64.hi_toNat (H ++ L)
    have := Proof.Sha512.Word64.lo_toNat (H ++ L)
    rw [hi_append] at *; rw [lo_append] at *
    omega
  rw [e]
  by_cases h : 2 ^ 32 ≤ L.toNat + y.toNat <;> simp [h] <;> omega

/-- The carry into the high 64 bits of the counter, by `adc` of their halves. -/
theorem adc_halves (L H : BitVec 32) (c : Bool) :
    (H + 0 + (BitVec.ofBool (decide (2 ^ 32 ≤ L.toNat + (0 : BitVec 32).toNat + c.toNat))).setWidth 32) ++
      (L + 0 + (BitVec.ofBool c).setWidth 32) = (H ++ L) + (BitVec.ofBool c).setWidth 64 := by
  apply Proof.Sha512.Word64.eq_of_lo_hi
  · rw [lo_append, Proof.Sha512.Word64.lo_add, lo_append]
    apply BitVec.eq_of_toNat_eq
    cases c <;> simp [lo]
  · rw [hi_append, Proof.Sha512.Word64.hi_add, hi_append, lo_append]
    have e1 : hi ((BitVec.ofBool c).setWidth 64) = 0 := by cases c <;> decide
    have e2 : (lo ((BitVec.ofBool c).setWidth 64)).toNat = c.toNat := by cases c <;> decide
    rw [e1, e2]
    by_cases h : 2 ^ 32 ≤ L.toNat + c.toNat <;> simp [h]

theorem carry_ofNat (T : Nat) : BitVec.ofNat 64 (T / 2 ^ 64) +
    (BitVec.ofBool (decide (2 ^ 64 ≤ (BitVec.ofNat 64 T).toNat + 128))).setWidth 64 =
    BitVec.ofNat 64 ((T + 128) / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  by_cases h : 2 ^ 64 ≤ T % 2 ^ 64 + 128
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_true, Bool.toNat_true]
    omega
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool, h,
      decide_false, Bool.toNat_false]
    omega

theorem advMem_reads {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) (m : Mem) :
    (VG.Proof.Blake2.X86.CompressB.advMem B m).readW (addr B blOff) 32 = m.readW (addr B blOff) 32 + 128 ∧
    (VG.Proof.Blake2.X86.CompressB.advMem B m).readW (addr B nOff) 32 = m.readW (addr B nOff) 32 - 1 ∧
    rd64 (VG.Proof.Blake2.X86.CompressB.advMem B m) B tOff = rd64 m B tOff + 128 ∧
    rd64 (VG.Proof.Blake2.X86.CompressB.advMem B m) B (tOff + 8) = rd64 m B (tOff + 8) +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (rd64 m B tOff).toNat + 128))).setWidth 64 ∧
    ∀ d, 280 ≤ d → d + 4 ≤ 512 → (VG.Proof.Blake2.X86.CompressB.advMem B m).readW (addr B d) 32 = m.readW (addr B d) 32 := by
  have r32 := VG.Proof.Blake2.X86.CompressB.rw32_ne hfit
  refine ⟨?_, ?_, ?_, ?_, fun d h1 h2 => ?_⟩
  · simp (disch := decide) only [VG.Proof.Blake2.X86.CompressB.advMem, r32, Mem.readW_writeW_self32]
  · simp (disch := decide) only [VG.Proof.Blake2.X86.CompressB.advMem, Mem.readW_writeW_self32]
  · simp (disch := decide) only [VG.Proof.Blake2.X86.CompressB.advMem, rd64, r32, Mem.readW_writeW_self32]
    exact VG.Proof.Blake2.X86.CompressB.add_halves _ _ 128
  · simp only [rd64]
    rw [show tOff + 8 + 4 = tOff + 12 from rfl]
    simp (disch := decide) only [VG.Proof.Blake2.X86.CompressB.advMem, r32, Mem.readW_writeW_self32]
    rw [VG.Proof.Blake2.X86.CompressB.adc_halves, decide_eq_decide.mpr (VG.Proof.Blake2.X86.CompressB.carry_halves _ _ 128)]
    rfl
  · simp only [VG.Proof.Blake2.X86.CompressB.advMem]
    rw [r32 _ _ (by decide) h2 (by simp only [nOff]; omega), r32 _ _ (by decide) h2 (by simp only [tOff]; omega),
      r32 _ _ (by decide) h2 (by simp only [tOff]; omega), r32 _ _ (by decide) h2 (by simp only [tOff]; omega),
      r32 _ _ (by decide) h2 (by simp only [tOff]; omega), r32 _ _ (by decide) h2 (by simp only [blOff]; omega)]

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) {i : Nat} (hi : i < VG.Proof.Blake2.X86.CompressB.nb s₀) {s : State}
    (hc : VG.Proof.Blake2.X86.CompressB.Common s₀ i s) :
    WP isa body s fun s' =>
      VG.Proof.Blake2.X86.CompressB.Common s₀ (i + 1) s' ∧ s'.zf = some (BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressB.nb s₀ - (i + 1)) == 0) := by
  have fV := hp.scr_fits
  have fS := hp.st_fits
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.stage1_ok hp hi hc) fun sb ⟨hR, fb, rdb, wrb, esib, espb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.rounds_ok fV esib (hp.acc wrb) hR 12) fun sc hR' => ?_)
  generalize hvR : (List.range 12).foldl (Spec.Blake2.round Spec.Blake2.b (VG.Proof.Blake2.X86.CompressB.blk s₀ i))
    (VG.Proof.Blake2.X86.CompressB.V0 (stateAt 64 s.mem ((VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64)) (VG.Proof.Blake2.X86.CompressB.t₀ s₀ + i * Spec.Blake2.blockBytes 64)
      (VG.Proof.Blake2.X86.CompressB.fl s₀)) = vR at hR'
  have esic : sc.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ := hR'.keep.esi esib
  have espc : sc.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀ := (hR'.keep.gpr _ (by decide)).trans espb
  have rdc : sc.rd = s₀.rd := hR'.keep.rd.trans rdb
  have wrc : sc.wr = s₀.wr := hR'.keep.wr.trans wrb
  have Fc : Frame [⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩] s.mem sc.mem := fb.trans hR'.frame
  have sub256 : ∀ r ∈ [(⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩ : Region)], ∃ r' ∈ [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀],
      Region.Sub r r' := fun r hr => ⟨VG.Proof.Blake2.X86.CompressB.scrR s₀, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hFc : Frame [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀] s₀.mem sc.mem := hc.frame.trans (Fc.sub sub256)
  -- XOR the work vector into the state.
  rw [WP.block_append_iff]
  unfold VG.Impl.Blake2.X86.CompressB.finish
  refine wp_movm (ea_of espc _) (hp.in_arg rdc (by decide) (by decide)) fun sd ud => ?_
  have ecxd : sd.gpr .ecx = VG.Proof.Blake2.X86.CompressB.st s₀ := by rw [ud.gpr]; exact hp.arg_frame hFc (i := 0) (by decide)
  refine WP.mono (VG.Proof.Blake2.X86.CompressB.finishWords_ok hp ecxd (by rw [ud.other _ (by decide), esic]) (by rw [ud.rd, rdc])
    (by rw [ud.wr, wrc])) fun se hF => ?_
  have esie : se.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ := by rw [hF.gpr _ (by decide), ud.other _ (by decide), esic]
  have wre : se.wr = s₀.wr := by rw [hF.wr, ud.wr, wrc]
  have Fe : Frame [VG.Proof.Blake2.X86.CompressB.stR s₀] sc.mem se.mem := by rw [← ud.mem]; exact hF.frame
  -- Advance.
  refine WP.mono (VG.Proof.Blake2.X86.CompressB.advance_ok fV esie (hp.acc wre)) fun sf ⟨mf, zf, gf, rdf, wrf⟩ => ?_
  obtain ⟨ab, an, at', ah, ao⟩ := VG.Proof.Blake2.X86.CompressB.advMem_reads fV se.mem
  rw [← mf] at ab an at' ah ao
  have hs32 : ∀ d, 256 ≤ d → d + 4 ≤ 512 →
      se.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 := fun d h1 h2 => by
    rw [hp.high_frame (.inr Fe) h1 h2, hp.high_frame (.inl Fc) h1 h2]
  have hs64 : ∀ d, 256 ≤ d → d + 8 ≤ 512 → rd64 se.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) d = rd64 s.mem (VG.Proof.Blake2.X86.CompressB.scr s₀) d :=
    fun d h1 h2 => by simp only [rd64]; rw [hs32 _ h1 (by omega), hs32 _ (by omega) h2]
  have hnb : VG.Proof.Blake2.X86.CompressB.nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hn : se.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) nOff) 32 - 1 = BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressB.nb s₀ - (i + 1)) := by
    rw [hs32 _ (by decide) (by decide), hc.n, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have Ff : Frame [VG.Proof.Blake2.X86.CompressB.stR s₀, VG.Proof.Blake2.X86.CompressB.scrR s₀] s₀.mem sf.mem := by
    refine (hFc.trans (Fe.mono (by simp))).trans ?_
    rw [mf]; exact (VG.Proof.Blake2.X86.CompressB.advMem_frame hp _).mono (by simp)
  refine ⟨⟨?_, ?_, ?_, ?_, Ff, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [zf, hn]⟩
  · rw [gf _ (by decide), esie]
  · rw [gf _ (by decide), hF.gpr _ (by decide), ud.other _ (by decide), espc]
  · rw [rdf, hF.rd, ud.rd, rdc]
  · rw [wrf, wre]
  · rw [Proof.Blake2.compressBlocks_succ, ← hc.state, VG.Proof.Blake2.X86.CompressB.F_eq, hvR]
    apply Vector.ext; intro j hj
    have hst : ∀ r ∈ [VG.Proof.Blake2.X86.CompressB.scrR s₀], Region.Disjoint ⟨(VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64, 64⟩ r := by
      simpa using hp.st_scr
    have hst' : ∀ r ∈ [(⟨(VG.Proof.Blake2.X86.CompressB.scr s₀).setWidth 64, 256⟩ : Region)],
        Region.Disjoint ⟨(VG.Proof.Blake2.X86.CompressB.st s₀).setWidth 64, 64⟩ r := by
      simpa using hp.st_scr.sub_right (Region.sub_prefix (by omega))
    rw [VG.Proof.Blake2.X86.CompressB.stateAt_rd64 fS _ hj, Vector.getElem_ofFn, mf,
      rd64_frame (VG.Proof.Blake2.X86.CompressB.advMem_frame hp _) hst fS (by omega), FI.state hF hj, ud.mem,
      hR'.holds j (by omega), hR'.holds (j + 8) (by omega), rd64_frame Fc hst' fS (by omega),
      ← VG.Proof.Blake2.X86.CompressB.stateAt_rd64 fS _ hj]
    rfl
  · intro p hp'
    have := VG.Proof.Blake2.X86.CompressB.saved_bounds p hp'
    rw [ao _ (by omega) this.2, hs32 _ (by omega) this.2]
    exact hc.saved p hp'
  · rw [ab, hs32 _ (by decide) (by decide), hc.bl]
    simp only [VG.Proof.Blake2.X86.CompressB.blkAddr]
    rw [BitVec.add_assoc, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl,
      BitVec.ofNat_add_ofNat]
    rfl
  · rw [an, hn]
  · rw [at', hs64 _ (by decide) (by decide), hc.tlo, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl,
      BitVec.ofNat_add_ofNat]
    congr 1
    simp only [Spec.Blake2.blockBytes]; omega
  · rw [ah, hs64 _ (by decide) (by decide), hs64 _ (by decide) (by decide), hc.thi, hc.tlo,
      VG.Proof.Blake2.X86.CompressB.carry_ofNat]
    congr 2
    simp only [Spec.Blake2.blockBytes]; omega
  · rw [show fOff = 280 from rfl]
    simp only [rd64]
    rw [ao _ (by decide) (by decide), ao _ (by decide) (by decide), hs32 _ (by decide) (by decide),
      hs32 _ (by decide) (by decide)]
    exact hc.f

end VG.Proof.Blake2.X86.CompressB

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressB.Lit`. -/
section

/-!
# BLAKE2b on x86 (32-bit): the code as literals

The compression function is fully unrolled (about 6,500 instructions): its
literal (`materialize_code`) spares the kernel building the instructions in
every check that evaluates the code (constant time, `spSafe`), and the
streaming functions call it.
-/

namespace VG.Impl.Blake2.X86.CompressB

materialize_code VG.Impl.Blake2.X86.CompressB.compress

end VG.Impl.Blake2.X86.CompressB

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified`. -/
section

/-!
# BLAKE2b compression function on x86 (32-bit): the whole function

The prologue and epilogue, `correct` (the loop over the blocks), constant time,
and `compress_verified` against `compressX86 b`
(`Proof/Blake2/X86/Contract.lean`), moved to the shared contract of
`Spec/Blake2/Contract.lean` (`compressB_verified`).
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue stateAt compressBlocks)
open VG.Proof.Sha512.X86 (Acc rd64 rd64_frame)
open VG.Proof.Sha256.X86.Stream (contains_addr)

/-! ## The prologue -/

theorem pro_eq : prologue = (.mov .eax (.mem ⟨.esp, 28⟩) :: (Spill.saveCode .eax saved ++
      ([.mov .esi (.reg .eax)] : List Instr))) ++
    (([.mov .eax (.mem ⟨.esp, 8⟩), .store ⟨.esi, 256⟩ .eax,
      .mov .eax (.mem ⟨.esp, 16⟩), .store ⟨.esi, 264⟩ .eax,
      .mov .eax (.mem ⟨.esp, 20⟩), .store ⟨.esi, 268⟩ .eax,
      .mov .eax (.imm 0), .store ⟨.esi, 272⟩ .eax, .store ⟨.esi, 276⟩ .eax] : List Instr) ++
    (([.mov .eax (.mem ⟨.esp, 24⟩), .mov .ecx (.imm 0), .alu .cmp .ecx (.reg .eax),
      .alu .sbb .ecx (.reg .ecx), .store ⟨.esi, 280⟩ .ecx, .store ⟨.esi, 284⟩ .ecx] : List Instr) ++
    ([.mov .eax (.mem ⟨.esp, 12⟩), .store ⟨.esi, 260⟩ .eax, .alu .test .eax (.reg .eax)] :
      List Instr))) := rfl

/-- The final block flag as the prologue computes it: `0 - 0 - (0 < x)`. -/
def flag32 (x : BitVec 32) : BitVec 32 :=
  0 - 0 - (BitVec.ofBool (decide ((0 : BitVec 32).toNat < x.toNat))).setWidth 32

theorem flag32_eq (x : BitVec 32) : VG.Proof.Blake2.X86.CompressB.flag32 x ++ VG.Proof.Blake2.X86.CompressB.flag32 x = VG.Proof.Blake2.X86.CompressB.flagW (x != 0) := by
  by_cases h : x = 0
  · subst h; decide
  · have : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h' | h'
      · exact absurd (BitVec.eq_of_toNat_eq h') h
      · exact h'
    have h' : decide ((0 : BitVec 32).toNat < x.toNat) = true := decide_eq_true this
    simp only [VG.Proof.Blake2.X86.CompressB.flag32, h', VG.Proof.Blake2.X86.CompressB.flagW, bne_iff_ne, ne_eq, h, not_false_eq_true, ite_true]
    decide

/-- The memory after saving the callee-saved registers. -/
abbrev proMem₁ (s₀ : State) : Mem := Spill.saveMem s₀.mem (addr (VG.Proof.Blake2.X86.CompressB.scr s₀)) s₀.gpr saved

/-- And the block's address and the counter. -/
def proMem₂ (s₀ : State) : Mem :=
  (((((VG.Proof.Blake2.X86.CompressB.proMem₁ s₀).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 256) (VG.Proof.Blake2.X86.CompressB.bp s₀)).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 264)
    (arg s₀ 3)).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 268) (arg s₀ 4)).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 272)
    (0 : BitVec 32)).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 276) (0 : BitVec 32)

/-- And the flag. -/
def proMem₃ (s₀ : State) : Mem :=
  ((VG.Proof.Blake2.X86.CompressB.proMem₂ s₀).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 280) (VG.Proof.Blake2.X86.CompressB.flag32 (arg s₀ 5))).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 284)
    (VG.Proof.Blake2.X86.CompressB.flag32 (arg s₀ 5))

/-- The memory after the prologue. -/
def proMem (s₀ : State) : Mem := (VG.Proof.Blake2.X86.CompressB.proMem₃ s₀).writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) 260) (arg s₀ 2)

theorem save_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ ∧ s₁.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = VG.Proof.Blake2.X86.CompressB.proMem s₀ ∧ s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have hsa : ∀ (m : Mem) (v : BitVec 32) {d e : Nat}, d + 4 ≤ 512 → 4 ≤ e → e + 4 ≤ 32 →
      (m.writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) v).readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 = m.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 :=
    fun m v d e hd he he' => Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he')
      (contains_addr hd (by omega) hp.scr_fits)) (by decide)
  have i8 := hp.in_arg (s := s₀) rfl (d := 8) (by omega) (by omega)
  have i12 := hp.in_arg (s := s₀) rfl (d := 12) (by omega) (by omega)
  have i16 := hp.in_arg (s := s₀) rfl (d := 16) (by omega) (by omega)
  have i20 := hp.in_arg (s := s₀) rfl (d := 20) (by omega) (by omega)
  have i24 := hp.in_arg (s := s₀) rfl (d := 24) (by omega) (by omega)
  have i28 := hp.in_arg (s := s₀) rfl (d := 28) (by omega) (by omega)
  have a8 : s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 8) 32 = VG.Proof.Blake2.X86.CompressB.bp s₀ := rfl
  have a12 : s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 12) 32 = arg s₀ 2 := rfl
  have a16 : s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 16) 32 = arg s₀ 3 := rfl
  have a20 : s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 20) 32 = arg s₀ 4 := rfl
  have a24 : s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 24) 32 = arg s₀ 5 := rfl
  have a28 : s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) 28) 32 = VG.Proof.Blake2.X86.CompressB.scr s₀ := rfl
  have hout : ∀ d, d + 4 ≤ 512 → InRegions s₀.wr (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 4 := hp.acc (s := s₀) rfl
  -- The arguments, read after writes to `scratch`.
  have r₁ : ∀ e, 4 ≤ e → e + 4 ≤ 32 →
      (VG.Proof.Blake2.X86.CompressB.proMem₁ s₀).readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 := by
    intro e h1 h2
    exact Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h => hp.arg_scr.sep (hp.arg_contains h1 h2)
      (contains_addr (by have := VG.Proof.Blake2.X86.CompressB.saved_bounds p h; omega) (by omega) hp.scr_fits)
  have r₂ : ∀ e, 4 ≤ e → e + 4 ≤ 32 →
      (VG.Proof.Blake2.X86.CompressB.proMem₂ s₀).readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 := by
    intro e h1 h2; simp (disch := omega) only [VG.Proof.Blake2.X86.CompressB.proMem₂, hsa, r₁]
  have r₃ : ∀ e, 4 ≤ e → e + 4 ≤ 32 →
      (VG.Proof.Blake2.X86.CompressB.proMem₃ s₀).readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.esp₀ s₀) e) 32 := by
    intro e h1 h2; simp (disch := omega) only [VG.Proof.Blake2.X86.CompressB.proMem₃, hsa, r₂]
  rw [VG.Proof.Blake2.X86.CompressB.pro_eq, WP.block_append_iff]
  refine WP.mono (Q := fun (s : State) => s.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ ∧ s.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀ ∧ s.rd = s₀.rd ∧
    s.wr = s₀.wr ∧ s.mem = VG.Proof.Blake2.X86.CompressB.proMem₁ s₀) ?_ fun s₁ ⟨e₁, p₁, d₁, w₁, m₁⟩ => ?_
  · refine Wp.wp_ldm rfl i28 fun s₁ u₁ => ?_
    refine Spill.save_ok saved (fun p h => by
        rw [u₁.gpr, u₁.wr]; exact hout _ (by have := VG.Proof.Blake2.X86.CompressB.saved_bounds p h; omega))
      fun s₂ u₂ => Wp.wp_mov fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl,
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)], by rw [u₃.rd, u₂.rd, u₁.rd],
        by rw [u₃.wr, u₂.wr, u₁.wr], ?_⟩
    rw [u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s : State) => s.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ ∧ s.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀ ∧ s.rd = s₀.rd ∧
    s.wr = s₀.wr ∧ s.mem = VG.Proof.Blake2.X86.CompressB.proMem₂ s₀) ?_ fun s₂ ⟨e₂, p₂, d₂, w₂, m₂⟩ => ?_
  · apply WP.of_runBlock
    simp (config := {decide := true}) (disch := decide) only [runBlock_cons, runBlock_nil,
      runStep_some, exec, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
      RegUpd.wr_setReg, State.load32, State.store32, e₁, p₁, d₁, w₁, m₁, i8, i16, i20, a8, a16, a20,
      hout, r₁, hsa, ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left', VG.Proof.Blake2.X86.CompressB.proMem₂]
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s : State) => s.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀ ∧ s.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀ ∧ s.rd = s₀.rd ∧
    s.wr = s₀.wr ∧ s.mem = VG.Proof.Blake2.X86.CompressB.proMem₃ s₀) ?_ fun s₃ ⟨e₃, p₃, d₃, w₃, m₃⟩ => ?_
  · apply WP.of_runBlock
    simp (config := {decide := true}) (disch := decide) only [runBlock_cons, runBlock_nil,
      runStep_some, exec, execAlu, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.cf_arithFlags, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, State.load32,
      State.store32, e₂, p₂, d₂, w₂, m₂, i24, a24, hout, r₂, ite_true, ite_false, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Blake2.X86.CompressB.proMem₃, VG.Proof.Blake2.X86.CompressB.flag32]
  · apply WP.of_runBlock
    simp (config := {decide := true}) (disch := decide) only [runBlock_cons, runBlock_nil,
      runStep_some, exec, execAlu, readSrc, ea_mk, RegUpd.gpr_setReg, RegUpd.mem_setReg,
      RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_arithFlags, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, State.load32,
      State.store32, e₃, p₃, d₃, w₃, m₃, i12, a12, hout, r₃, ite_true, ite_false, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left', VG.Proof.Blake2.X86.CompressB.proMem]

theorem proMem_frame {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) : Frame [VG.Proof.Blake2.X86.CompressB.scrR s₀] s₀.mem (VG.Proof.Blake2.X86.CompressB.proMem s₀) := by
  have c : ∀ d : Nat, d + 4 ≤ 512 → (VG.Proof.Blake2.X86.CompressB.scrR s₀).Contains (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) (32 / 8) :=
    fun d hd => contains_addr hd (by omega) hp.scr_fits
  have m := List.mem_singleton_self (VG.Proof.Blake2.X86.CompressB.scrR s₀)
  simp only [VG.Proof.Blake2.X86.CompressB.proMem, VG.Proof.Blake2.X86.CompressB.proMem₃, VG.Proof.Blake2.X86.CompressB.proMem₂]
  exact (((((((((Spill.saveMem_frame m _ _ _ _ fun p h => c _ (by have := VG.Proof.Blake2.X86.CompressB.saved_bounds p h; omega)).writeW
    m _ (c 256 (by omega))).writeW m _
    (c 264 (by omega))).writeW m _ (c 268 (by omega))).writeW m _ (c 272 (by omega))).writeW m _
    (c 276 (by omega))).writeW m _ (c 280 (by omega))).writeW m _ (c 284 (by omega))).writeW m _
    (c 260 (by omega)))

theorem common_zero {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) {s₁ : State} (hesi : s₁.gpr .esi = VG.Proof.Blake2.X86.CompressB.scr s₀)
    (hesp : s₁.gpr .esp = VG.Proof.Blake2.X86.CompressB.esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = VG.Proof.Blake2.X86.CompressB.proMem s₀) : VG.Proof.Blake2.X86.CompressB.Common s₀ 0 s₁ := by
  have r32 := VG.Proof.Blake2.X86.CompressB.rw32_ne hp.scr_fits
  have hF : Frame [VG.Proof.Blake2.X86.CompressB.scrR s₀] s₀.mem s₁.mem := hm ▸ VG.Proof.Blake2.X86.CompressB.proMem_frame hp
  have rd : ∀ d, s₁.mem.readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 = (VG.Proof.Blake2.X86.CompressB.proMem s₀).readW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) d) 32 := by
    intro d; rw [hm]
  refine ⟨hesi, hesp, hrd, hwr, hF.mono (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Proof.Blake2.compressBlocks_zero]
    apply Vector.ext; intro j hj
    rw [VG.Proof.Blake2.X86.CompressB.stateAt_rd64 hp.st_fits _ hj, VG.Proof.Blake2.X86.CompressB.stateAt_rd64 hp.st_fits _ hj]
    exact rd64_frame hF (by simpa using hp.st_scr) hp.st_fits (by omega)
  · have w : ∀ {m : Mem} (e : Nat), VG.Proof.Blake2.X86.CompressB.Saved s₀ m → e + 4 ≤ 512 → (∀ p ∈ saved, p.2 + 4 ≤ e ∨ e + 4 ≤ p.2) →
        ∀ v : BitVec 32, VG.Proof.Blake2.X86.CompressB.Saved s₀ (m.writeW (addr (VG.Proof.Blake2.X86.CompressB.scr s₀) e) v) :=
      fun e h he hsep v => h.writeW_addr (w := 32) hp.scr_fits (fun p hp' => by have := VG.Proof.Blake2.X86.CompressB.saved_bounds p hp'; omega) he hsep v
    rw [hm]
    exact w _ (w _ (w _ (w _ (w _ (w _ (w _ (w _ (Spill.saveMem_saved_addr s₀.mem _ VG.Proof.Blake2.X86.CompressB.saved_fits (by have := hp.scr_fits; omega)) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _
  · simp (disch := decide) only [rd, VG.Proof.Blake2.X86.CompressB.proMem, VG.Proof.Blake2.X86.CompressB.proMem₃, VG.Proof.Blake2.X86.CompressB.proMem₂, VG.Proof.Blake2.X86.CompressB.proMem₁, r32, Mem.readW_writeW_self32, blOff, VG.Proof.Blake2.X86.CompressB.blkAddr,
      Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · simp (disch := decide) only [rd, VG.Proof.Blake2.X86.CompressB.proMem, VG.Proof.Blake2.X86.CompressB.proMem₃, VG.Proof.Blake2.X86.CompressB.proMem₂, VG.Proof.Blake2.X86.CompressB.proMem₁, Mem.readW_writeW_self32, nOff, Nat.sub_zero,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (disch := decide) only [rd64, rd, VG.Proof.Blake2.X86.CompressB.proMem, VG.Proof.Blake2.X86.CompressB.proMem₃, VG.Proof.Blake2.X86.CompressB.proMem₂, VG.Proof.Blake2.X86.CompressB.proMem₁, r32, Mem.readW_writeW_self32, tOff,
      Nat.zero_mul, Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp (disch := decide) only [rd64, rd, VG.Proof.Blake2.X86.CompressB.proMem, VG.Proof.Blake2.X86.CompressB.proMem₃, VG.Proof.Blake2.X86.CompressB.proMem₂, VG.Proof.Blake2.X86.CompressB.proMem₁, r32, Mem.readW_writeW_self32, tOff,
      Nat.zero_mul, Nat.add_zero, Nat.reduceAdd]
    rw [Nat.div_eq_of_lt (BitVec.isLt _)]
    rfl
  · simp (disch := decide) only [rd64, rd, VG.Proof.Blake2.X86.CompressB.proMem, VG.Proof.Blake2.X86.CompressB.proMem₃, VG.Proof.Blake2.X86.CompressB.proMem₂, VG.Proof.Blake2.X86.CompressB.proMem₁, r32, Mem.readW_writeW_self32, fOff,
      Nat.reduceAdd]
    exact VG.Proof.Blake2.X86.CompressB.flag32_eq _

/-! ## The epilogue -/

theorem epilogue_eq :
    epilogue = Spill.restoreCode .esi ([(.ebx, 288), (.edi, 296), (.ebp, 300)] ++ [(.esi, 292)]) ++ [] := rfl

theorem restore_ok {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) {s : State} (hc : VG.Proof.Blake2.X86.CompressB.Common s₀ (VG.Proof.Blake2.X86.CompressB.nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [VG.Proof.Blake2.X86.CompressB.epilogue_eq]
  exact Spill.restoreBase_ok _ (by decide)
    (fun p h => by rw [hc.esi]; exact hp.in_scr hc.wr (VG.Proof.Blake2.X86.CompressB.saved_bounds p (by revert p h; decide)).2)
    (by rw [hc.esi]; exact hc.saved.sub (by decide)) fun s' r' =>
      WP.block_nil ⟨r'.abi (by decide) (by decide) hc.esp, r'.mem⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s₀) :
    WP isa VG.Impl.Blake2.X86.CompressB.compress s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Blake2.compressX86 Spec.Blake2.b).post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Blake2.X86.CompressB.save_ok hp) fun s₁ ⟨hesi, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.X86.CompressB.Common s₀ (VG.Proof.Blake2.X86.CompressB.nb s₀)) ?_ fun s₂ hc =>
    WP.mono (VG.Proof.Blake2.X86.CompressB.restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt 64 s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := VG.Proof.Blake2.X86.CompressB.common_zero hp hesi hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Blake2.X86.CompressB.nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [VG.Proof.Blake2.X86.CompressB.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Blake2.X86.CompressB.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Blake2.X86.CompressB.nb s₀ - i ∧ i < VG.Proof.Blake2.X86.CompressB.nb s₀ ∧ VG.Proof.Blake2.X86.CompressB.Common s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Blake2.X86.CompressB.Common s₀ (VG.Proof.Blake2.X86.CompressB.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hc⟩
      refine WP.mono (VG.Proof.Blake2.X86.CompressB.body_ok hp hi hc) fun s' ⟨hc', hz'⟩ => ?_
      have hnb : VG.Proof.Blake2.X86.CompressB.nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
      by_cases hlast : i + 1 = VG.Proof.Blake2.X86.CompressB.nb s₀
      · left
        refine ⟨?_, hlast ▸ hc'⟩
        rw [Proof.Sha256.X86.Stream.eval_ne, hz', ← hlast, Nat.sub_self]; rfl
      · right
        have hne : VG.Proof.Blake2.X86.CompressB.nb s₀ - (i + 1) ≠ 0 := by omega
        have h0 : (BitVec.ofNat 32 (VG.Proof.Blake2.X86.CompressB.nb s₀ - (i + 1)) == 0) = false := by
          rw [beq_eq_false_iff_ne]
          intro h'
          have h'' := congrArg BitVec.toNat h'
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h''
          exact hne h''
        refine ⟨?_, VG.Proof.Blake2.X86.CompressB.nb s₀ - (i + 1), by omega, i + 1, rfl, by omega, hc'⟩
        rw [Proof.Sha256.X86.Stream.eval_ne, hz', h0]; rfl
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Blake2.X86.CompressB.nb s₀) s₁ ⟨0, rfl, hpos, hc₀⟩

/-! ## Constant time -/

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 512], argLen := 32,
    argBases := [(4, 0), (28, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.Blake2.X86.CompressB.Pre s) : VG.X86.Taint.Wf VG.Proof.Blake2.X86.CompressB.τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Blake2.X86.CompressB.τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [VG.Proof.Blake2.X86.CompressB.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : (VG.Proof.Blake2.compressX86 Spec.Blake2.b).pre s₁)
    (h₂ : (VG.Proof.Blake2.compressX86 Spec.Blake2.b).pre s₂) (hpub : (VG.Proof.Blake2.compressX86 Spec.Blake2.b).pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.Blake2.X86.CompressB.τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := VG.Proof.Blake2.X86.CompressB.pre_of _ h₁; have hp₂ := VG.Proof.Blake2.X86.CompressB.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Blake2.X86.CompressB.wf₀ hp₁, VG.Proof.Blake2.X86.CompressB.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Blake2.X86.CompressB.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Blake2.X86.CompressB.stR, VG.Proof.Blake2.X86.CompressB.scrR, VG.Proof.Blake2.X86.CompressB.st, VG.Proof.Blake2.X86.CompressB.scr, ha 0 (by decide), ha 6 (by decide)]
  · simp only [VG.Proof.Blake2.X86.CompressB.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.esp_fits; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.esp_fits; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-! ## Results -/

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0, 0, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x401D then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Blake2.X86.CompressB.satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 28⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 512⟩]

theorem sat_pre : (VG.Proof.Blake2.compressX86 Spec.Blake2.b).pre VG.Proof.Blake2.X86.CompressB.satState := by
  have a0 : arg VG.Proof.Blake2.X86.CompressB.satState 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Blake2.X86.CompressB.satState 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Blake2.X86.CompressB.satState 2 = 0 := by decide
  have a6 : arg VG.Proof.Blake2.X86.CompressB.satState 6 = 0x3000 := by decide
  have e : argAddr VG.Proof.Blake2.X86.CompressB.satState 0 = 0x4004 := by decide
  simp only [VG.Proof.Blake2.compressX86, Spec.Blake2.blockBytes, a0, a1, a2, a6, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem compress_verified : Verified X86.target VG.Impl.Blake2.X86.CompressB.compress (VG.Proof.Blake2.compressX86 Spec.Blake2.b) :=
  ⟨fun s hs => VG.Proof.Blake2.X86.CompressB.correct (VG.Proof.Blake2.X86.CompressB.pre_of s hs),
    VG.Taint.constantTime (A := taint) VG.Proof.Blake2.X86.CompressB.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Blake2.X86.CompressB.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨VG.Proof.Blake2.X86.CompressB.satState, VG.Proof.Blake2.X86.CompressB.sat_pre⟩⟩

theorem compressB_verified :
    Verified X86.target VG.Impl.Blake2.X86.CompressB.compress (Spec.Blake2.compressBContract X86.abi) :=
  compress_verified.of_implies (by
    sig_implies [Spec.Blake2.compressBContract, Spec.Blake2.compressBSig, Proof.Blake2.compressX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes, Spec.Blake2.blockBytes]
      [satState, satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.Blake2.X86.CompressB.satState)

end VG.Proof.Blake2.X86.CompressB

end
