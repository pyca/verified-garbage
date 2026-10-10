import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquareWide
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareBlock
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareDiagonalStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRow

/-! ## AdxSquareWideWord -/
section

/-! Word-level equations retain both carry flags across stores. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem store_ok {s : State} {B : Addr} {Z e j k : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 ≤ Z) :
    WP isa (.block [.store (ix .r8 .r14 (8 * k)) .r11]) s fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * j + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of ∧ Keep [] s t := by
  refine WP.mono (WP.keep [] (Q := fun t =>
      t.mem = s.mem.writeW (off B (e + 8 * j + 8 * k)) (s.gpr .r11) ∧
      t.cf = s.cf ∧ t.of = s.of) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2, kt⟩
  xrun [ea_ixk s h8 h14 k, hs.st hZ]

theorem word_ok {s : State} {B : Addr} {Z e eb j k : Nat} {hi prev : Reg} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 ≤ Z) (hZb : eb + 8 * j + 8 * k + 8 ≤ Z)
    (hc : s.cf = some c) (ho : s.of = some o)
    (d1 : hi ≠ .r11) (d2 : prev ≠ hi) (d3 : prev ≠ .r11) (d4 : hi ≠ .r8) (d5 : hi ≠ .r14) :
    WP isa (.block (AdxSquareWide.word k hi prev)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      (word t.mem B (e + 8 * j + 8 * k)).toNat +
        2 ^ 64 * ((t.gpr hi).toNat + c'.toNat + o'.toNat) =
        (word s.mem B (e + 8 * j + 8 * k)).toNat +
        (s.gpr .rdx).toNat * (word s.mem B (eb + 8 * j + 8 * k)).toNat +
        (s.gpr prev).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) 8 s.mem t.mem ∧ Keep [hi, .r11] s t := by
  have hn := hs.nowrap
  unfold AdxSquareWide.word
  rw [WP.block_append_iff]
  refine WP.mono (wordA_ok s (readSrc_word hs (ea_ixk s h9 h14 k) hZb)
    (readSrc_word hs (ea_ixk s h8 h14 k) hZ) hc ho d1 d2 d3 d4 (by decide) d5 (by decide))
    fun a ⟨c', o', ca, oa, eq, ka⟩ => ?_
  refine WP.mono (store_ok (hs.congr ka.2.2.2) ((ka.gpr (by simp [Ne.symm d4])).trans h8)
    ((ka.gpr (by simp [Ne.symm d5])).trans h14) hZ) fun t ⟨hm, ct, ot, kt⟩ => ?_
  refine ⟨c', o', ct.trans ca, ot.trans oa, ?_, ?_, (ka.keep.trans kt).mono (by simp)⟩
  · rw [kt.gpr (by simp), hm, word_writeW_self]
    omega_using [eq]
  · rw [hm, ka.2.1]; exact writeW_outside _ _ _ (by omega)
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWidePair -/
section

/-! A pair returns the high half to `rcx`, leaving both flags live. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem pair_ok {s : State} {B : Addr} {Z e eb j k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 16 ≤ Z) (hZb : eb + 8 * j + 8 * k + 16 ≤ Z)
    (sb : eb + 8 * j + 8 * k + 16 ≤ e + 8 * j + 8 * k ∨
      e + 8 * j + 8 * k + 16 ≤ eb + 8 * j + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareWide.pair k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * j + 8 * k) 2 +
        2 ^ 128 * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * j + 8 * k) 2 +
        (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j + 8 * k) 2 +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) 16 s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  have hn := hs.nowrap
  unfold AdxSquareWide.pair
  rw [WP.block_append_iff]
  refine WP.mono (word_ok hs h8 h9 h14 (by omega) (by omega) hc ho
    (by decide) (by decide) (by decide) (by decide) (by decide))
    fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
  refine WP.mono (word_ok (k := k + 1) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h8)
    ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
    (by omega) (by omega) hca hoa (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
  have he : e + 8 * j + 8 * (k + 1) = e + 8 * j + 8 * k + 8 := by omega
  have heb : eb + 8 * j + 8 * (k + 1) = eb + 8 * j + 8 * k + 8 := by omega
  rw [he, heb, ka.gpr (by decide)] at et
  rw [he] at outt
  have lo : word t.mem B (e + 8 * j + 8 * k) = word a.mem B (e + 8 * j + 8 * k) :=
    outt.word (by omega) (by omega)
  have ti : word a.mem B (e + 8 * j + 8 * k + 8) = word s.mem B (e + 8 * j + 8 * k + 8) :=
    outa.word (by omega) (by omega)
  have bi : word a.mem B (eb + 8 * j + 8 * k + 8) = word s.mem B (eb + 8 * j + 8 * k + 8) :=
    outa.word (by omega) (by omega)
  rw [ti, bi] at et
  refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
  · rw [AdxSquare.wv2, AdxSquare.wv2, AdxSquare.wv2, lo]
    simp only [Nat.mul_add]
    rw [Nat.mul_left_comm (s.gpr .rdx).toNat]
    omega_using [ea, et]
  · exact (outa.mono (o' := e + 8 * j + 8 * k) (n' := 16) (Nat.le_refl _) (by omega)).trans
      (outt.mono (o' := e + 8 * j + 8 * k) (n' := 16) (by omega) (by omega))
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWideChain -/
section

/-! Composing live-carry pairs into an unrolled multiply-add chain. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem chain_ok (n : Nat) {s : State} {B : Addr} {Z e eb j k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j)
    (hZ : e + 8 * j + 8 * k + 8 * (2 * n) ≤ Z) (hZb : eb + 8 * j + 8 * k + 8 * (2 * n) ≤ Z)
    (sb : eb + 8 * j + 8 * k + 8 * (2 * n) ≤ e + 8 * j + 8 * k ∨
      e + 8 * j + 8 * k + 8 * (2 * n) ≤ eb + 8 * j + 8 * k)
    (hc : s.cf = some c) (ho : s.of = some o) :
    WP isa (.block (AdxSquareWide.chain n k)) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧
      wv t.mem B (e + 8 * j + 8 * k) (2 * n) +
        2 ^ (64 * (2 * n)) * ((t.gpr .rcx).toNat + c'.toNat + o'.toNat) =
        wv s.mem B (e + 8 * j + 8 * k) (2 * n) +
        (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j + 8 * k) (2 * n) +
        (s.gpr .rcx).toNat + c.toNat + o.toNat ∧
      Outside B (e + 8 * j + 8 * k) (8 * (2 * n)) s.mem t.mem ∧ Keep [.rax, .r11, .rcx] s t := by
  induction n generalizing s k c o with
  | zero =>
    apply WP.block_nil
    exact ⟨c, o, hc, ho, by simp [wv], Outside.refl _ _ _ _, VG.Proof.MlKem.X86_64.Keep.refl _ _⟩
  | succ n ih =>
    have hn := hs.nowrap
    rw [AdxSquareWide.chain, WP.block_append_iff]
    refine WP.mono (pair_ok hs h8 h9 h14 (by omega) (by omega) (by omega) hc ho)
      fun a ⟨ca, oa, hca, hoa, ea, outa, ka⟩ => ?_
    refine WP.mono (ih (k := k + 2) (hs.congr ka.2.2) ((ka.gpr (by decide)).trans h8)
      ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
      (by omega) (by omega) (by omega) hca hoa)
      fun t ⟨ct, ot, hct, hot, et, outt, kt⟩ => ?_
    have he : e + 8 * j + 8 * (k + 2) = e + 8 * j + 8 * k + 8 * 2 := by omega
    have heb : eb + 8 * j + 8 * (k + 2) = eb + 8 * j + 8 * k + 8 * 2 := by omega
    rw [he, heb, ka.gpr (by decide)] at et
    rw [he] at outt
    have lo : wv t.mem B (e + 8 * j + 8 * k) 2 = wv a.mem B (e + 8 * j + 8 * k) 2 :=
      outt.wv (by omega) (by omega)
    have ti : wv a.mem B (e + 8 * j + 8 * k + 8 * 2) (2 * n) =
        wv s.mem B (e + 8 * j + 8 * k + 8 * 2) (2 * n) := outa.wv (by omega) (by omega)
    have bi : wv a.mem B (eb + 8 * j + 8 * k + 8 * 2) (2 * n) =
        wv s.mem B (eb + 8 * j + 8 * k + 8 * 2) (2 * n) := outa.wv (by omega) (by omega)
    rw [ti, bi] at et
    refine ⟨ct, ot, hct, hot, ?_, ?_, (ka.trans kt).mono (by simp)⟩
    · rw [show 2 * (n + 1) = 2 + 2 * n by omega, wv_add, wv_add, wv_add, lo,
        show 64 * (2 + 2 * n) = 128 + 64 * (2 * n) by omega, Nat.pow_add]
      grind
    · exact (outa.mono (o' := e + 8 * j + 8 * k) (n' := 8 * (2 * (n + 1))) (Nat.le_refl _) (by omega)).trans
        (outt.mono (o' := e + 8 * j + 8 * k) (n' := 8 * (2 * (n + 1))) (by omega) (by omega))
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWideBlock -/
section

/-! Closing a sixteen-word chain and advancing its public counter. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem carry_bound {R V T X Y C H : Nat} (hR : 0 < R) (hT : T < R)
    (hX : X < 2 ^ 64) (hY : Y < R) (hC : C < 2 ^ 64)
    (he : V + R * H = T + X * Y + C) : H < 2 ^ 64 := by
  have hp : X * Y ≤ (2 ^ 64 - 1) * (R - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hb : R * H < R * 2 ^ 64 := by omega_using [he, hp, hR, hT, hC]
  exact Nat.lt_of_mul_lt_mul_left hb

theorem block_ok {s : State} {B : Addr} {Z e eb j w : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hZ : e + 8 * j + 128 ≤ Z) (hZb : eb + 8 * j + 128 ≤ Z)
    (sb : eb + 8 * j + 128 ≤ e + 8 * j ∨ e + 8 * j + 128 ≤ eb + 8 * j)
    (hj : j + 16 < 2 ^ 64) (hw : w < 2 ^ 64) :
    WP isa (.block AdxSquareWide.block) s fun t =>
      wv t.mem B (e + 8 * j) 16 + 2 ^ 1024 * (t.gpr .rcx).toNat =
        wv s.mem B (e + 8 * j) 16 + (s.gpr .rdx).toNat * wv s.mem B (eb + 8 * j) 16 + (s.gpr .rcx).toNat ∧
      Outside B (e + 8 * j) 128 s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧
      t.zf = some (decide (j + 16 = w)) ∧ Keep [.rsi, .rax, .r11, .rcx, .r14] s t := by
  unfold AdxSquareWide.block
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorRsi_ok s) fun a ⟨_, ca, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (chain_ok 8 (k := 0) (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans h8)
    ((ka.gpr (by decide)).trans h9) ((ka.gpr (by decide)).trans h14)
    (by simpa using hZ) (by simpa using hZb) (by simpa using sb) ca oa)
    fun b ⟨cb, ob, hcb, hob, eq, out, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Bool.toNat_false, ka.2.1] at eq out
  rw [ka.gpr (r := .rdx) (by decide), ka.gpr (r := .rcx) (by decide)] at eq
  rw [WP.block_append_iff]
  refine WP.mono (close_ok b hcb hob (by decide)) fun d ⟨cd, od, _, _, ed, kd⟩ => ?_
  have hT := wv_lt s.mem B (e + 8 * j) 16
  have hB := wv_lt s.mem B (eb + 8 * j) 16
  simp only [Nat.reduceMul] at hT hB
  have hX := (s.gpr .rdx).isLt
  have hC := (s.gpr .rcx).isLt
  have hb : (b.gpr .rcx).toNat + cb.toNat + ob.toNat < 2 ^ 64 :=
    carry_bound (R := 2 ^ 1024) (V := wv b.mem B (e + 8 * j) 16)
      (T := wv s.mem B (e + 8 * j) 16) (X := (s.gpr .rdx).toNat)
      (Y := wv s.mem B (eb + 8 * j) 16) (C := (s.gpr .rcx).toNat)
      (Nat.two_pow_pos 1024) hT hX hB hC eq
  have eclose : (d.gpr .rcx).toNat = (b.gpr .rcx).toNat + cb.toNat + ob.toNat := by
    have := Bool.toNat_le cd; have := Bool.toNat_le od
    omega_using [ed, hb, this]
  have k := (ka.keep.trans kb).trans kd.keep
  have h14d := (k.gpr (by decide)).trans h14
  have hbxd := (k.gpr (by decide)).trans hbx
  have tail : WP isa (.block [.alu .add .r14 (.imm 16), .alu .cmp .r14 (.reg .rbx)]) d fun t =>
      t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧ t.zf = some (decide (j + 16 = w)) ∧
      t.mem = d.mem ∧ Keep [.r14] d t := by
    refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (j + 16) ∧
      t.zf = some (decide (j + 16 = w)) ∧ t.mem = d.mem) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2, kt⟩
    have ha : BitVec.ofNat 64 j + 16 = BitVec.ofNat 64 (j + 16) := by
      rw [BitVec.ofNat_add]; rfl
    xrun [h14d, hbxd, ha, ofNat_sub_beq hj hw]
  refine WP.mono tail fun t ⟨ht14, htz, hm, kt⟩ => ⟨?_, ?_, ht14, htz, (k.trans kt).mono (by simp)⟩
  · rw [hm, kd.2.1, kt.gpr (by decide), eclose]; exact eq
  · rw [hm, kd.2.1]; exact out
end VG.Proof.Bignum.X86_64.AdxSquareWide

end

/-! ## AdxSquareWideRow -/
section

/-! A long-block row, with the existing row as the general-size fallback. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareWide
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxSquare (RowInv)

theorem blocks_ok {s₀ s : State} {B : Addr} {Z e eb a w : Nat}
    (h8 : s₀.gpr .r8 = off B e) (h9 : s₀.gpr .r9 = off B eb)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hw16 : w % 16 = 0) (haw : 16 * a < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb)
    (hI : RowInv s₀ B Z e eb (16 * a) s) :
    WP isa (.loop (.block AdxSquareWide.block) .ne) s (RowInv s₀ B Z e eb w) := by
  refine wp_upto (a := a) (N := w / 16) (by omega)
    (fun k t => RowInv s₀ B Z e eb (16 * k) t ∧ t.gpr .rbx = BitVec.ofNat 64 w) ?_ ?_ ⟨hI, hbx⟩
  · intro k _ hk t h
    obtain ⟨h, hbx'⟩ := h
    have kp := h.keep
    refine WP.mono (block_ok h.scr ((kp.gpr (by decide)).trans h8)
      ((kp.gpr (by decide)).trans h9) h.r14 hbx'
      (by omega) (by omega) (by omega) (by omega) (by omega))
      fun t' ⟨hv, ho, h14, hz, kt⟩ => ⟨?_, ?_, (kt.gpr (by decide)).trans hbx'⟩
    · exact hz.trans (congrArg some (decide_eq_decide.mpr (by omega_using [hk, hw16])))
    · have step := @RowInv.step s₀ t t' B Z e eb (16 * k) 16 w h (by omega_using [hk, hw16] : 16 * k + 16 ≤ w) hZ hZb sb (by simpa only [Nat.reduceMul] using hv) ho h14 (kt.mono (by decide))
      rw [show 16 * (k + 1) = 16 * k + 16 by omega_using []]
      exact step
  · intro t h
    have he : 16 * (w / 16) = w := by omega
    exact he ▸ h.1

theorem and15 (w : Nat) (hw : w < 2 ^ 64) :
    BitVec.ofNat 64 w &&& 15 = BitVec.ofNat 64 (w % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw,
    show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat]
  omega

theorem row_ok {s : State} {B : Addr} {Z e eb w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B e) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 w) (hw1 : 0 < w) (hw : w < 2 ^ 60)
    (hZ : e + 8 * w ≤ Z) (hZb : eb + 8 * w ≤ Z)
    (sb : eb + 8 * w ≤ e ∨ e + 8 * w ≤ eb) :
    WP isa AdxSquareWide.row s fun t =>
      wv t.mem B e w + 2 ^ (64 * w) * (t.gpr .rcx).toNat =
        wv s.mem B e w + (s.gpr .rdx).toNat * wv s.mem B eb w ∧
      Outside B e (8 * w) s.mem t.mem ∧ t.gpr .r14 = BitVec.ofNat 64 w ∧
      Keep [.rsi, .rax, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx] s t := by
  have guard : WP isa (.block [.mov .rbx (.reg .rbp), .alu .and .rbx (.imm 15), .alu .cmp .rbx (.imm 0)]) s
      fun t => t.zf = some (decide (w % 16 = 0)) ∧ t.mem = s.mem ∧ Keep [.rbx] s t := by
    refine WP.mono (WP.keep [.rbx] (Q := fun t => t.zf = some (decide (w % 16 = 0)) ∧ t.mem = s.mem)
      ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
    xrun [hbp, and15 w (by omega)]
    change ((BitVec.ofNat 64 w &&& 15) - BitVec.ofNat 64 0 == 0) = _
    rw [and15 w (by omega)]
    exact ofNat_sub_beq (by omega) (by decide)
  unfold AdxSquareWide.row
  refine WP.seq (WP.mono guard fun a ⟨hz, hm, ka⟩ => ?_)
  have ha8 := (ka.gpr (by decide)).trans h8
  have ha9 := (ka.gpr (by decide)).trans h9
  have habp := (ka.gpr (by decide)).trans hbp
  by_cases h16 : w % 16 = 0
  · refine WP.ite true (by simp [eval, hz, h16]) (fun _ => ?_) (by simp)
    have init : WP isa (.block [.mov .rbx (.reg .rbp), .mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0)]) a
        fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧ t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧
          t.mem = a.mem ∧ Keep [.rbx, .rcx, .r14] a t := by
      refine WP.mono (WP.keep [.rbx, .rcx, .r14] (Q := fun t => t.gpr .rbx = BitVec.ofNat 64 w ∧
        t.gpr .rcx = 0 ∧ t.gpr .r14 = 0 ∧ t.mem = a.mem) ?_ rfl)
        fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
      xrun [habp]
    refine WP.seq (WP.mono init fun b ⟨hbx, hcx, h14, hmb, kb⟩ => ?_)
    have kab := ka.trans kb
    have inv : RowInv b B Z e eb 0 b :=
      ⟨hs.congr kab.2.2, Keep.refl _ _, h14, Outside.refl _ _ _ _, by simp [wv]⟩
    refine WP.mono (blocks_ok (a := 0) ((kab.gpr (by decide)).trans h8)
      ((kab.gpr (by decide)).trans h9) hbx h16 (by omega) hw hZ hZb sb inv)
      fun t hi => ⟨?_, ?_, hi.r14, (kab.trans hi.keep).mono (by decide)⟩
    · have hv := hi.val
      rw [hmb, hm, kab.gpr (by decide), hcx] at hv
      simpa using hv
    · have ho := hi.out; rw [hmb, hm] at ho; exact ho
  · refine WP.ite false (by simp [eval, hz, h16]) (by simp) (fun _ => ?_)
    refine WP.mono (AdxSquare.macRow_ok (hs.congr ka.2.2) ha8 ha9 habp hw hZ hZb sb)
      fun t ⟨hv, ho, h14, kt⟩ => ⟨?_, ?_, h14, (ka.trans kt).mono (by decide)⟩
    · rw [hm, ka.gpr (by decide)] at hv; exact hv
    · rw [hm] at ho; exact ho
end VG.Proof.Bignum.X86_64.AdxSquareWide

end
