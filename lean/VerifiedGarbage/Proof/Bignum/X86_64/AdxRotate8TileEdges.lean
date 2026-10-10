import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Frame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tail
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Head

/-! ## AdxRotate8Product -/
section

/-! The full register-resident product of two eight-word blocks. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem productN_ok {s : State} {B : Addr} {Z eU eO eN n : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hp : s.gpr .rbp = off B eN)
    (ho : s.gpr .rsi = off B eO) (huZ : eU + 8 * n ≤ Z)
    (hoZ : eO + 8 * n ≤ Z) (hnZ : eN + 64 ≤ Z)
    (hsepU : eU + 8 * n ≤ eO) (hsepN : eN + 64 ≤ eO) :
    WP isa (AdxRotate8.productN n) s fun t =>
      wv t.mem B eO n + 2 ^ (64 * n) * cols t =
        cols s + wv s.mem B eU n * wv s.mem B eN 8 ∧
      Outside B eO (8 * n) s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add],
      Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold AdxRotate8.productN
    refine WP.seq (WP.mono (ih (by omega) (by omega) (by omega)) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    refine WP.mono (productStep_ok sa ((ka.gpr (by decide)).trans hc)
      ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho)
      (by omega) (by omega) hnZ) fun t ⟨vt, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega) (by omega)
    have mu : word a.mem B (eU + 8 * n) = word s.mem B (eU + 8 * n) := oa.word (by omega) (by omega)
    have lo : wv t.mem B eO n = wv a.mem B eO n := ot.wv (by omega) (by omega)
    refine ⟨?_, (oa.mono (o' := eO) (n' := 8 * (n + 1)) (by omega) (by omega)).trans
      (ot.mono (o' := eO) (n' := 8 * (n + 1)) (by omega) (by omega)), (ka.trans kt).mono (by decide)⟩
    rw [mn, mu] at vt
    rw [wv, wv, lo, pow64_succ]
    grind
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8MiddleBody -/
section

/-! One input block and eight multiplier rows, with the overflow retained. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem middleBody_ok {s : State} {B : Addr} {Z eU eO eN : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hp : s.gpr .rbp = off B eN)
    (ho : s.gpr .rsi = off B eO) (he : 8 ≤ eU) (huZ : eU + 64 ≤ Z)
    (hoZ : eO + 64 ≤ Z) (hnZ : eN + 64 ≤ Z)
    (hsepU : eU + 64 ≤ eO) (hsepN : eN + 64 ≤ eU - 8) :
    WP isa AdxRotate8.middleBody s fun t =>
      wv t.mem B eO 8 + 2 ^ 512 * (cols t + (word t.mem B (eU - 8)).toNat) =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 +
          wv s.mem B eU 8 * wv s.mem B eN 8 ∧
      (word t.mem B (eU - 8)).toNat ≤ 2 ∧ BlockOut B (eU - 8) eO 64 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.middleBody
  refine WP.seq (WP.mono (accumulate_ok hs hc ho he (by omega) hoZ) fun a ⟨va, ba, oa, ka⟩ => ?_)
  refine WP.mono (productN_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hc)
    ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho) huZ hoZ hnZ hsepU (by omega))
    fun t ⟨vt, ot, kt⟩ => ?_
  have wn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega) (by omega)
  have wu : wv a.mem B eU 8 = wv s.mem B eU 8 := oa.wv (by omega) (by omega)
  have wc : word t.mem B (eU - 8) = word a.mem B (eU - 8) := ot.word (by omega) (by omega)
  rw [wn, wu] at vt
  refine ⟨?_, by rw [wc]; exact ba, (BlockOut.first oa).trans (BlockOut.second ot), (ka.trans kt).mono (by decide)⟩
  rw [wc]
  omega_using [va, vt]
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8Next -/
section

/-! Public block pointers and loop endpoint. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem nextBlock_ok {s : State} {B : Addr} {Z w eU j : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hj : j + 8 ≤ w)
    (hp : s.gpr .rbp = off B (slot w aN + 8 * j))
    (ho : s.gpr .rsi = off B (eU + 8 * j)) :
    WP isa (.block AdxRotate8.nextBlock) s fun t =>
      t.gpr .rbp = off B (slot w aN + 8 * (j + 8)) ∧
      t.gpr .rsi = off B (eU + 8 * (j + 8)) ∧
      t.zf = some (decide (j + 8 = w)) ∧ t.mem = s.mem ∧ Keep [.rbp, .rsi, .rax] s t := by
  have hn := hs.nowrap
  have hN := slot_le (w := w) (show aN < 8 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  have a8 (e : Nat) : off B (e + 8 * j) + 64 = off B (e + 8 * (j + 8)) := by
    change off (off B (e + 8 * j)) 64 = off B (e + 8 * (j + 8))
    rw [off_off]
    congr 1
  have w8 : ((BitVec.ofNat 64 w + BitVec.ofNat 64 w) +
      (BitVec.ofNat 64 w + BitVec.ofNat 64 w)) +
      ((BitVec.ofNat 64 w + BitVec.ofNat 64 w) + (BitVec.ofNat 64 w + BitVec.ofNat 64 w)) = BitVec.ofNat 64 (8 * w) := by
    simp only [← BitVec.ofNat_add]; congr 1; omega
  have ep : BitVec.ofNat 64 (8 * w) + off B (slot w aN) = off B (slot w aN + 8 * w) := by
    rw [BitVec.add_comm]
    exact off_off B (slot w aN) (8 * w)
  have hz : ((off B (slot w aN + 8 * (j + 8)) - off B (slot w aN + 8 * w)) == 0) = decide (j + 8 = w) := by
    rw [off_sub_beq B (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.rbp, .rsi, .rax] (Q := fun t =>
      t.gpr .rbp = off B (slot w aN + 8 * (j + 8)) ∧
      t.gpr .rsi = off B (eU + 8 * (j + 8)) ∧
      t.zf = some (decide (j + 8 = w)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩
  unfold AdxRotate8.nextBlock
  xrun [State.ea, hdr, hdi, hdrOff, hp, ho, a8, hl sW (by decide),
    show BitVec.signExtend 64 (64 : BitVec 32) = (64 : BitVec 64) from rfl, hl (sArr aN) (by decide), hH.hw, hH.harr aN (by decide), w8, ep, hz]
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8MiddleInv -/
section

/-! An invariant for all modulus blocks above the eight cancellation words. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure MiddleInv (s₀ : State) (B : Addr) (Z w e i : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  rcx : s.gpr .rcx = off B e
  rbp : s.gpr .rbp = off B (slot w aN + 64 * (i + 1))
  rsi : s.gpr .rsi = off B (e + 64 * (i + 1))
  keep : Keep mmRegs s₀ s
  out : BlockOut B (e - 8) (e + 64) (64 * i) s₀.mem s.mem
  val : wv s.mem B (e + 64) (8 * i) + 2 ^ (512 * i) * (cols s + (word s.mem B (e - 8)).toNat) =
    cols s₀ + (word s₀.mem B (e - 8)).toNat + wv s₀.mem B (e + 64) (8 * i) +
      wv s₀.mem B e 8 * wv s₀.mem B (slot w aN + 64) (8 * i)

theorem middleStep_ok {s₀ s : State} {B : Addr} {Z w e n i : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1)) (hi : i < n)
    (he : hdrBytes + 16 ≤ e) (heZ : e + 8 * (w + 8) ≤ Z)
    (hsep : slot w aN + 8 * w ≤ e - 8) (h : MiddleInv s₀ B Z w e i mi s) :
    WP isa AdxRotate8.middle s fun t =>
      t.zf = some (decide (i + 1 = n)) ∧ MiddleInv s₀ B Z w e (i + 1) mi t := by
  have hn := h.scr.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  unfold AdxRotate8.middle
  refine WP.seq (WP.mono (middleBody_ok h.scr h.rcx h.rbp h.rsi (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)) fun a ⟨va, _, oa, ka⟩ => ?_)
  have hha : Hdr a.mem B w mi := h.hdr.of_outside
    (oa.outside (a := e - 8) (b := 64 * (i + 2) + 8) (by omega) (by omega) (by omega) (by omega)) (by omega)
  have haP : a.gpr .rbp = off B (slot w aN + 8 * (8 * (i + 1))) := by
    rw [ka.gpr (by decide), h.rbp]; congr 1; omega
  have haO : a.gpr .rsi = off B (e + 8 * (8 * (i + 1))) := by
    rw [ka.gpr (by decide), h.rsi]; congr 1; omega
  refine WP.mono (nextBlock_ok (h.scr.congr ka.2.2) ((ka.gpr (by decide)).trans h.rdi)
    hha hZ (by omega) haP haO) fun t ⟨hp, ho, hz, hm, kt⟩ => ?_
  have oall : BlockOut B (e - 8) (e + 64) (64 * (i + 1)) s₀.mem a.mem :=
    (h.out.mono (by omega) (by omega)).trans (oa.mono (by omega) (by omega))
  have vT : wv s.mem B (e + 64 * (i + 1)) 8 = wv s₀.mem B (e + 64 * (i + 1)) 8 :=
    h.out.wv (by omega) (by omega) (by omega)
  have vU : wv s.mem B e 8 = wv s₀.mem B e 8 := h.out.wv (by omega) (by omega) (by omega)
  have vN : wv s.mem B (slot w aN + 64 * (i + 1)) 8 = wv s₀.mem B (slot w aN + 64 * (i + 1)) 8 :=
    h.out.wv (by omega) (by omega) (by omega)
  have vp : wv a.mem B (e + 64) (8 * i) = wv s.mem B (e + 64) (8 * i) :=
    oa.wv (by omega) (by omega) (by omega)
  rw [vT, vU, vN] at va
  refine ⟨?_, ⟨h.scr.congr ((ka.trans kt).2.2), hm ▸ hha,
    ((ka.trans kt).gpr (by decide)).trans h.rdi,
    ((ka.trans kt).gpr (by decide)).trans h.rcx, ?_, ?_,
    (h.keep.trans (ka.trans kt)).mono (by decide), ?_, ?_⟩⟩
  · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [hp]; congr 1; omega
  · rw [ho]; congr 1; omega
  · rw [hm]; exact oall
  · rw [hm, cols_keep kt (by decide)]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, wv_add, wv_add, wv_add, vp,
      show e + 64 + 8 * (8 * i) = e + 64 * (i + 1) by omega,
      show slot w aN + 64 + 8 * (8 * i) = slot w aN + 64 * (i + 1) by omega,
      show 64 * (8 * i) = 512 * i by omega,
      show 512 * (i + 1) = 512 * i + 512 by omega, Nat.pow_add]
    exact extend_blocks h.val va
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8Middle -/
section

/-! The loop over all higher modulus blocks, including the one-block case. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem middles_ok {s : State} {B : Addr} {Z w e n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hH : Hdr s.mem B w mi) (hdi : s.gpr .rdi = B)
    (hc : s.gpr .rcx = off B e) (hp : s.gpr .rbp = off B (slot w aN + 64))
    (ho : s.gpr .rsi = off B (e + 64)) (hz : s.zf = some (decide (n = 0)))
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1))
    (he : hdrBytes + 16 ≤ e) (heZ : e + 8 * (w + 8) ≤ Z)
    (hsep : slot w aN + 8 * w ≤ e - 8) :
    WP isa (.ite .ne (.loop AdxRotate8.middle .ne) (.block [])) s (MiddleInv s B Z w e n mi) := by
  have h0 : MiddleInv s B Z w e 0 mi s := ⟨hs, hH, hdi, hc,
    by simpa only [Nat.zero_add, Nat.mul_one] using hp,
    by simpa only [Nat.zero_add, Nat.mul_one] using ho,
    Keep.refl _ _, BlockOut.refl _ _ _ _ _, by
      simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]⟩
  by_cases hn : n = 0
  · refine WP.ite false (by simp [eval, hz, hn]) (by simp) (fun _ => WP.block_nil ?_)
    rw [hn]; exact h0
  · refine WP.ite true (by simp [eval, hz, hn]) (fun _ => ?_) (by simp)
    exact wp_upto (a := 0) (N := n) (by omega) (MiddleInv s B Z w e · mi)
      (fun _ _ hi _ h => middleStep_ok hZ hw hi he heZ hsep h) (fun _ h => h) h0
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8TileEdges -/
section

/-! Initial columns, zero block carry, and public tile advance. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem tileBegin_ok {s : State} {B : Addr} {Z w e : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B e) (he : e + 64 ≤ Z) :
    WP isa AdxRotate8.tileBegin s fun t => cols t = wv s.mem B e 8 ∧
      t.gpr .rbp = off B (slot w aN) ∧ t.gpr .rsi = off B e ∧ t.mem = s.mem ∧
      Keep [.rbp, .rsi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aN)) 8 :=
    hs.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega)
  unfold AdxRotate8.tileBegin
  refine WP.seq (WP.mono (WP.keep [.rbp, .rsi] (Q := fun t =>
    t.gpr .rbp = off B (slot w aN) ∧ t.gpr .rsi = off B e ∧ t.mem = s.mem) ?_ rfl)
    fun a ⟨⟨hp, ho, hm⟩, ka⟩ => ?_)
  · xrun [State.ea, hdr, hdi, hdrOff, hc, hl, hH.harr aN (by decide)]
  · refine WP.mono (loadCols_ok (hs.congr ka.2.2) ho he) fun t ⟨hv, kt⟩ => ?_
    exact ⟨hm ▸ hv, (kt.gpr (by decide)).trans hp, (kt.gpr (by decide)).trans ho,
      kt.2.1.trans hm, (ka.trans kt.keep).mono (by simp)⟩

theorem clearCarry_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B e) (he : 8 ≤ e) (hZ : e ≤ Z) :
    WP isa (.block AdxRotate8.clearCarry) s fun t =>
      word t.mem B (e - 8) = 0 ∧ Outside B (e - 8) 8 s.mem t.mem ∧ Keep [.rax] s t := by
  unfold AdxRotate8.clearCarry
  rw [show ([Instr.mov32 .rax (.imm 0), .store AdxRotate8.blockCarry .rax]) =
    [.mov32 .rax (.imm 0)] ++ [.store AdxRotate8.blockCarry .rax] from rfl, WP.block_append_iff]
  refine WP.mono (movZero_ok s .rax) fun a ⟨za, _, _, ka⟩ => ?_
  refine WP.mono (storeMem_ok (hs.congr ka.2.2.2) (ea_carry ((ka.gpr (by decide)).trans hc) he)
    (show e - 8 + 8 ≤ Z by omega)) fun t ⟨wt, ot, kt⟩ => ?_
  exact ⟨wt.trans za, by rw [ka.2.1] at ot; exact ot, (ka.keep.trans kt).mono (by simp)⟩

theorem tileEnd_ok {s : State} {B : Addr} {Z w e : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w mi)
    (hZ : slot w 8 ≤ Z) (hc : s.gpr .rcx = off B e) (he : hdrBytes ≤ e)
    (heZ : e + 72 ≤ Z) :
    WP isa (.block AdxRotate8.tileEnd) s fun t =>
      word t.mem B (e + 48) = s.gpr .rax ∧ t.gpr .rcx = off B (e + 64) ∧
      t.zf = some (decide (e + 64 = slot w aTmp)) ∧ Outside B (e + 48) 8 s.mem t.mem ∧ Keep [.rcx] s t := by
  have hn := hs.nowrap
  have hT := slot_le (w := w) (show aTmp < 8 by decide)
  unfold AdxRotate8.tileEnd
  rw [show ([Instr.store (AdxRotate8.at_ .rcx 48) .rax, .alu .add .rcx (.imm 64),
    .alu .cmp .rcx (.mem (hdr (sArr aTmp)))]) = [.store (AdxRotate8.at_ .rcx 48) .rax] ++
      [.alu .add .rcx (.imm 64), .alu .cmp .rcx (.mem (hdr (sArr aTmp)))] from rfl, WP.block_append_iff]
  refine WP.mono (storeAt_ok hs hc (show e + 48 + 8 ≤ Z by omega)) fun a ⟨wa, oa, ka⟩ => ?_
  have sa := hs.congr ka.2.2
  have ha := hH.of_outside oa (by omega)
  have hca := (ka.gpr (by simp)).trans hc
  have hda := (ka.gpr (by simp)).trans hdi
  have hl : InRegions (a.rd ++ a.wr) (off B (8 * sArr aTmp)) 8 :=
    sa.ld (by have := hdr_lt_slot w 8 (show sArr aTmp < 32 by decide); omega)
  have adv : off B e + BitVec.signExtend 64 (64 : BitVec 32) = off B (e + 64) := by
    change off (off B e) 64 = off B (e + 64)
    exact off_off _ _ _
  refine WP.mono (WP.keep [.rcx] (Q := fun t =>
    t.gpr .rcx = off B (e + 64) ∧ t.zf = some (decide (e + 64 = slot w aTmp)) ∧ t.mem = a.mem) ?_ rfl)
    fun t ⟨⟨hc', hz, hm⟩, kt⟩ => ?_
  · xrun [State.ea, hdr, hda, hdrOff, hca, adv, hl, ha.harr aTmp (by decide),
      off_sub_beq B (show e + 64 < 2 ^ 64 by omega) (show slot w aTmp < 2 ^ 64 by omega)]
  · exact ⟨by rw [hm]; exact wa, hc', hz, by rw [hm]; exact oa, (ka.trans kt).mono (by simp)⟩
end VG.Proof.Bignum.X86_64.AdxRotate8

end
