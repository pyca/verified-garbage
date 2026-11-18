module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcRow
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Memory
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Core
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Accumulate
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Store
import VerifiedGarbage.Proof.Bignum.X86_64.AdxDualAddClose
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! ### `Bignum.X86_64.AdxRotate8Tail`, which the modules that import this one used -/

section

/-! ### `Bignum.X86_64.AdxRotate8TileEdges`, which the modules that import this one used -/

section

/-! ### `Bignum.X86_64.AdxRotate8Frame`, which only this module used -/

section

/-! The reduction block writes one carry word and a separate output range. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Proof.Bignum.X86_64

def BlockOut (B : Addr) (c e n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs B x < c ∨ c + 8 ≤ ofs B x) → (ofs B x < e ∨ e + n ≤ ofs B x) → m' x = m x

theorem BlockOut.refl (B : Addr) (c e n : Nat) (m : Mem) : BlockOut B c e n m m := fun _ _ _ => rfl

theorem BlockOut.first {B : Addr} {c e n : Nat} {m m' : Mem} (h : Outside B c 8 m m') :
    BlockOut B c e n m m' := fun x hx _ => h x hx

theorem BlockOut.second {B : Addr} {c e n : Nat} {m m' : Mem} (h : Outside B e n m m') :
    BlockOut B c e n m m' := fun x _ hx => h x hx

theorem BlockOut.trans {B : Addr} {c e n : Nat} {m m' m'' : Mem}
    (h : BlockOut B c e n m m') (h' : BlockOut B c e n m' m'') : BlockOut B c e n m m'' :=
  fun x hc he => (h' x hc he).trans (h x hc he)

theorem BlockOut.mono {B : Addr} {c e n e' n' : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (he : e' ≤ e) (hn : e + n ≤ e' + n') : BlockOut B c e' n' m m' :=
  fun x hc hx => h x hc (by omega_using [he, hn, hx])

theorem BlockOut.outside {B : Addr} {c e n a b : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (hc : a ≤ c) (hc' : c + 8 ≤ a + b)
    (he : a ≤ e) (he' : e + n ≤ a + b) : Outside B a b m m' :=
  fun x hx => h x (by omega_using [hc, hc', hx]) (by omega_using [he, he', hx])

theorem BlockOut.word {B : Addr} {c e n d : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (hc : d + 8 ≤ c ∨ c + 8 ≤ d)
    (he : d + 8 ≤ e ∨ e + n ≤ d) (hd : d + 8 ≤ 2 ^ 64) : word m' B d = word m B d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off B (by omega_using [hd, hi])]; omega_using [hc, hi])
    (by rw [ofs_off B (by omega_using [hd, hi])]; omega_using [he, hi])).symm).symm

theorem BlockOut.wv {B : Addr} {c e n d k : Nat} {m m' : Mem}
    (h : BlockOut B c e n m m') (hc : d + 8 * k ≤ c ∨ c + 8 ≤ d)
    (he : d + 8 * k ≤ e ∨ e + n ≤ d) (hd : d + 8 * k ≤ 2 ^ 64) : wv m' B d k = wv m B d k :=
  wv_congr fun _ hi => h.word (by omega_using [hc, hi]) (by omega_using [he, hi]) (by omega_using [hd, hi])
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end


/-! ## AdxRotate8Product -/

@[expose] public section

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
    refine WP.seq (WP.mono (ih (by omega_arith) (by omega_arith) (by omega_arith)) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    refine WP.mono (productStep_ok sa ((ka.gpr (by decide)).trans hc)
      ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho)
      (by omega_arith) (by omega_arith) hnZ) fun t ⟨vt, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega_arith) (by omega_arith)
    have mu : word a.mem B (eU + 8 * n) = word s.mem B (eU + 8 * n) := oa.word (by omega_arith) (by omega_arith)
    have lo : wv t.mem B eO n = wv a.mem B eO n := ot.wv (by omega_arith) (by omega_arith)
    refine ⟨?_, (oa.mono (o' := eO) (n' := 8 * (n + 1)) (by omega_arith) (by omega_arith)).trans
      (ot.mono (o' := eO) (n' := 8 * (n + 1)) (by omega_arith) (by omega_arith)), (ka.trans kt).mono (by decide)⟩
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
    (hsepU : eU + 64 ≤ eO) (hsepN : eN + 64 ≤ eU - 8)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa AdxRotate8.middleBody s fun t =>
      wv t.mem B eO 8 + 2 ^ 512 * (cols t + (word t.mem B (eU - 8)).toNat) =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 +
          wv s.mem B eU 8 * wv s.mem B eN 8 ∧
      (word t.mem B (eU - 8)).toNat ≤ 1 ∧ BlockOut B (eU - 8) eO 64 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.middleBody
  refine WP.seq (WP.mono (accumulate_ok hs hc ho he (by omega_arith) hoZ hb) fun a ⟨va, ba, oa, ka⟩ => ?_)
  refine WP.mono (productN_ok (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hc)
    ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho) huZ hoZ hnZ hsepU (by omega_arith))
    fun t ⟨vt, ot, kt⟩ => ?_
  have wn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega_arith) (by omega_arith)
  have wu : wv a.mem B eU 8 = wv s.mem B eU 8 := oa.wv (by omega_arith) (by omega_arith)
  have wc : word t.mem B (eU - 8) = word a.mem B (eU - 8) := ot.word (by omega_arith) (by omega_arith)
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
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have a8 (e : Nat) : off B (e + 8 * j) + 64 = off B (e + 8 * (j + 8)) := by
    change off (off B (e + 8 * j)) 64 = off B (e + 8 * (j + 8))
    rw [off_off]
    congr 1
  have w8 : ((BitVec.ofNat 64 w + BitVec.ofNat 64 w) +
      (BitVec.ofNat 64 w + BitVec.ofNat 64 w)) +
      ((BitVec.ofNat 64 w + BitVec.ofNat 64 w) + (BitVec.ofNat 64 w + BitVec.ofNat 64 w)) = BitVec.ofNat 64 (8 * w) := by
    simp only [← BitVec.ofNat_add]; congr 1; omega_arith
  have ep : BitVec.ofNat 64 (8 * w) + off B (slot w aN) = off B (slot w aN + 8 * w) := by
    rw [BitVec.add_comm]
    exact off_off B (slot w aN) (8 * w)
  have hz : ((off B (slot w aN + 8 * (j + 8)) - off B (slot w aN + 8 * w)) == 0) = decide (j + 8 = w) := by
    rw [off_sub_beq B (by omega_arith) (by omega_arith)]
    exact decide_eq_decide.mpr (by omega_arith)
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
  bit : (word s.mem B (e - 8)).toNat ≤ 1
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
  refine WP.seq (WP.mono (middleBody_ok h.scr h.rcx h.rbp h.rsi (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) h.bit) fun a ⟨va, ba, oa, ka⟩ => ?_)
  have hha : Hdr a.mem B w mi := h.hdr.of_outside
    (oa.outside (a := e - 8) (b := 64 * (i + 2) + 8) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
  have haP : a.gpr .rbp = off B (slot w aN + 8 * (8 * (i + 1))) := by
    rw [ka.gpr (by decide), h.rbp]; congr 1; omega_arith
  have haO : a.gpr .rsi = off B (e + 8 * (8 * (i + 1))) := by
    rw [ka.gpr (by decide), h.rsi]; congr 1; omega_arith
  refine WP.mono (nextBlock_ok (h.scr.congr ka.2.2) ((ka.gpr (by decide)).trans h.rdi)
    hha hZ (by omega_arith) haP haO) fun t ⟨hp, ho, hz, hm, kt⟩ => ?_
  have oall : BlockOut B (e - 8) (e + 64) (64 * (i + 1)) s₀.mem a.mem :=
    (h.out.mono (by omega_arith) (by omega_arith)).trans (oa.mono (by omega_arith) (by omega_arith))
  have vT : wv s.mem B (e + 64 * (i + 1)) 8 = wv s₀.mem B (e + 64 * (i + 1)) 8 :=
    h.out.wv (by omega_arith) (by omega_arith) (by omega_arith)
  have vU : wv s.mem B e 8 = wv s₀.mem B e 8 := h.out.wv (by omega_arith) (by omega_arith) (by omega_arith)
  have vN : wv s.mem B (slot w aN + 64 * (i + 1)) 8 = wv s₀.mem B (slot w aN + 64 * (i + 1)) 8 :=
    h.out.wv (by omega_arith) (by omega_arith) (by omega_arith)
  have vp : wv a.mem B (e + 64) (8 * i) = wv s.mem B (e + 64) (8 * i) :=
    oa.wv (by omega_arith) (by omega_arith) (by omega_arith)
  rw [vT, vU, vN] at va
  refine ⟨?_, ⟨h.scr.congr ((ka.trans kt).2.2), hm ▸ hha,
    ((ka.trans kt).gpr (by decide)).trans h.rdi,
    ((ka.trans kt).gpr (by decide)).trans h.rcx, ?_, ?_,
    (h.keep.trans (ka.trans kt)).mono (by decide), ?_, by rw [hm]; exact ba, ?_⟩⟩
  · rw [hz]; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · rw [hp]; congr 1; omega_arith
  · rw [ho]; congr 1; omega_arith
  · rw [hm]; exact oall
  · rw [hm, cols_keep kt (by decide)]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega_arith, wv_add, wv_add, wv_add, vp,
      show e + 64 + 8 * (8 * i) = e + 64 * (i + 1) by omega_arith,
      show slot w aN + 64 + 8 * (8 * i) = slot w aN + 64 * (i + 1) by omega_arith,
      show 64 * (8 * i) = 512 * i by omega_arith,
      show 512 * (i + 1) = 512 * i + 512 by omega_arith, Nat.pow_add]
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
    (h0b : word s.mem B (e - 8) = 0)
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * (n + 1))
    (he : hdrBytes + 16 ≤ e) (heZ : e + 8 * (w + 8) ≤ Z)
    (hsep : slot w aN + 8 * w ≤ e - 8) :
    WP isa (.ite .ne (.loop AdxRotate8.middle .ne) (.block [])) s (MiddleInv s B Z w e n mi) := by
  have h0 : MiddleInv s B Z w e 0 mi s := ⟨hs, hH, hdi, hc,
    by simpa only [Nat.zero_add, Nat.mul_one] using hp,
    by simpa only [Nat.zero_add, Nat.mul_one] using ho,
    Keep.refl _ _, BlockOut.refl _ _ _ _ _, by rw [h0b]; decide, by
      simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]⟩
  by_cases hn : n = 0
  · refine WP.ite false (by simp [eval, hz, hn]) (by simp) (fun _ => WP.block_nil ?_)
    rw [hn]; exact h0
  · refine WP.ite true (by simp [eval, hz, hn]) (fun _ => ?_) (by simp)
    exact wp_upto (a := 0) (N := n) (by omega_arith) (MiddleInv s B Z w e · mi)
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
    hs.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_arith)
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
    (show e - 8 + 8 ≤ Z by omega_arith)) fun t ⟨wt, ot, kt⟩ => ?_
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
  refine WP.mono (storeAt_ok hs hc (show e + 48 + 8 ≤ Z by omega_arith)) fun a ⟨wa, oa, ka⟩ => ?_
  have sa := hs.congr ka.2.2
  have ha := hH.of_outside oa (by omega_arith)
  have hca := (ka.gpr (by simp)).trans hc
  have hda := (ka.gpr (by simp)).trans hdi
  have hl : InRegions (a.rd ++ a.wr) (off B (8 * sArr aTmp)) 8 :=
    sa.ld (by have := hdr_lt_slot w 8 (show sArr aTmp < 32 by decide); omega_arith)
  have adv : off B e + BitVec.signExtend 64 (64 : BitVec 32) = off B (e + 64) := by
    change off (off B e) 64 = off B (e + 64)
    exact off_off _ _ _
  refine WP.mono (WP.keep [.rcx] (Q := fun t =>
    t.gpr .rcx = off B (e + 64) ∧ t.zf = some (decide (e + 64 = slot w aTmp)) ∧ t.mem = a.mem) ?_ rfl)
    fun t ⟨⟨hc', hz, hm⟩, kt⟩ => ?_
  · xrun [State.ea, hdr, hda, hdrOff, hca, adv, hl, ha.harr aTmp (by decide),
      off_sub_beq B (show e + 64 < 2 ^ 64 by omega_arith) (show slot w aTmp < 2 ^ 64 by omega_arith)]
  · exact ⟨by rw [hm]; exact wa, hc', hz, by rw [hm]; exact oa, (ka.trans kt).mono (by simp)⟩
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end

end

/-! The final input block consumes both saved carries. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem ea_tileCarry {s : State} {B : Addr} {e : Nat} (hc : s.gpr .rcx = off B e) (he : 16 ≤ e) :
    s.ea AdxRotate8.tileCarry = off B (e - 16) := by
  change s.gpr .rcx + BitVec.ofInt 64 (-16) = off B (e - 16)
  rw [hc, show BitVec.ofInt 64 (-16) = 0 - BitVec.ofNat 64 16 from rfl]
  exact Offset.add_ofNat_add_neg B he

theorem tailAdd_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 16 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa (.block AdxRotate8.tailAdd) s fun t =>
      cols t + 2 ^ 512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 + (word s.mem B (eU - 16)).toNat ∧
      (t.gpr .rax).toNat ≤ 2 ∧ t.mem = s.mem ∧
      Keeps [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.tailAdd
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (carryIn_ok hs hc (by omega_using [he]) huZ hb) fun a ⟨ca,oa,ma,ka⟩ => ?_
  rw [show ([Instr.mov32 .rax (.imm 0), .mov .rdx (.mem AdxRotate8.tileCarry)] ++ _) =
    [Instr.mov32 .rax (.imm 0)] ++ ([.mov .rdx (.mem AdxRotate8.tileCarry)] ++ _) from rfl,
    WP.block_append_iff]
  refine WP.mono (movZero_ok a .rax) fun b ⟨zb,cb,ob,kb⟩ => ?_
  rw [WP.block_append_iff]
  have kab := ka.trans kb
  have hm := readSrc_word (hs.congr kab.2.2.2) (ea_tileCarry ((kab.gpr (by decide)).trans hc) he)
    (show eU - 16 + 8 ≤ Z by omega_using [he, huZ])
  refine WP.mono (movMem_ok b (dst := .rdx) hm) fun c ⟨dc,cc,oc,kc⟩ => ?_
  have kac := kab.trans kc
  rw [WP.block_append_iff]
  have srcA : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs c t →
      readSrc t (.mem (AdxRotate8.at_ .rsi (8*k))) = some (word s.mem B (eO+8*k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [AdxDualAdd.regs, AdxRotate8.at_]) (by intro r h; nomatch h),
      kac.readMem (by simp [AdxRotate8.at_]) (by intro r h; nomatch h)]
    exact readSrc_word hs (ea_at ho (8*k)) (by omega_using [hoZ, hk])
  have dc' : c.gpr .rdx = word s.mem B (eU - 16) := by rw [dc, kab.2.1]
  have zc : c.gpr .rax = 0 := (kc.gpr (by decide)).trans zb
  have srcB : ∀ k < 8, ∀ t, Keeps AdxDualAdd.regs c t →
      readSrc t (.reg (if k = 0 then .rdx else .rax)) =
        some (if k = 0 then word s.mem B (eU - 16) else 0) := by
    intro k _ t kt
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte, readSrc, kt.gpr (r := .rdx) (by decide), dc']
    · simp only [hk, ↓reduceIte, readSrc, kt.gpr (r := .rax) (by decide), zc]
  have cC : c.cf = some (decide ((word s.mem B (eU - 8)).toNat = 1)) := cc.trans (cb.trans ca)
  have oC : c.of = some false := oc.trans (ob.trans oa)
  refine WP.mono (AdxDualAdd.chain_ok c _ _ _ _ cC oC srcA srcB
    (fun _ _ _ h => nomatch h) (fun _ _ _ h => nomatch h)) fun d ⟨cd,od,hcd,hod,ed,kd⟩ => ?_
  refine WP.mono (AdxDualAdd.close_ok d hcd hod ((kd.gpr (by decide)).trans zc))
    fun t ⟨et,_,_,kt⟩ => ?_
  rw [number_words, cols_keep kac.keep (by decide)] at ed
  simp only [number, Nat.reduceEqDiff, ↓reduceIte,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero,
    Bool.toNat_false] at ed
  have bit : (decide ((word s.mem B (eU - 8)).toNat = 1)).toNat = (word s.mem B (eU - 8)).toNat := by
    rcases (show (word s.mem B (eU - 8)).toNat = 0 ∨ (word s.mem B (eU - 8)).toNat = 1 by omega_using [hb]) with h | h <;>
      rw [h] <;> rfl
  rw [bit] at ed
  refine ⟨?_, ?_, kt.2.1.trans (kd.2.1.trans kac.2.1),
    (kac.trans (kd.trans kt)).mono (by simp [AdxDualAdd.regs])⟩
  · rw [cols_keep kt.keep (by decide), et]; omega_using [ed]
  · rw [et]; have b1 := Bool.toNat_le cd; have b2 := Bool.toNat_le od; omega_using [b1, b2]

theorem tailCore_ok {s : State} {B : Addr} {Z eU eO : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (ho : s.gpr .rsi = off B eO)
    (he : 16 ≤ eU) (huZ : eU ≤ Z) (hoZ : eO + 64 ≤ Z)
    (hb : (word s.mem B (eU - 8)).toNat ≤ 1) :
    WP isa AdxRotate8.tailCore s fun t =>
      wv t.mem B eO 8 + 2 ^ 512 * (t.gpr .rax).toNat =
        cols s + (word s.mem B (eU - 8)).toNat + wv s.mem B eO 8 +
          (word s.mem B (eU - 16)).toNat ∧
      (t.gpr .rax).toNat ≤ 3 ∧ Outside B eO 64 s.mem t.mem ∧
      Keep [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.tailCore
  refine WP.seq (WP.mono (tailAdd_ok hs hc ho he huZ hoZ hb) fun b ⟨eb,bb,mb,kb⟩ => ?_)
  refine WP.mono (storeCols_ok (hs.congr kb.2.2.2) ((kb.gpr (by decide)).trans ho) hoZ)
    fun t ⟨vt, ot, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, (kb.keep.trans kt).mono (by decide)⟩
  · rw [vt, kt.gpr (r := .rax) (by simp)]
    omega_using [eb]
  · rw [kt.gpr (r := .rax) (by simp)]
    omega_using [bb]
  · rw [mb] at ot; exact ot
end VG.Proof.Bignum.X86_64.AdxRotate8

end

end

/-! ## AdxRotate8HeadStep -/

@[expose] public section

section

/-! A register cancellation step, with memory safety independent of the inverse. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem cols_mod (s : State) : cols s % 2 ^ 64 = (s.gpr .r8).toNat := by
  have h : cols s = (s.gpr .r8).toNat + 2 ^ 64 *
      ((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat + 2 ^ 128 * (s.gpr .r11).toNat +
      2 ^ 192 * (s.gpr .r12).toNat + 2 ^ 256 * (s.gpr .r13).toNat +
      2 ^ 320 * (s.gpr .r14).toNat + 2 ^ 384 * (s.gpr .r15).toNat) := by
    unfold cols; omega_using []
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (s.gpr .r8).isLt]

theorem cancel_low {s t : State} {B : Addr} {eN : Nat} {mi : BitVec 64}
    (hinv : ((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0)
    (heq : (t.gpr .rbx).toNat + 2 ^ 64 * cols t =
      cols s + (digitValue s mi).toNat * wv s.mem B eN 8) : t.gpr .rbx = 0 := by
  have e := congrArg (· % 2 ^ 64) heq
  have lo := mont_low (s.gpr .r8).toNat mi.toNat (word s.mem B eN).toNat hinv
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_eq_of_lt (t.gpr .rbx).isLt, cols_mod,
    AdxSquare.wv_mod_word _ _ _ (show 1 ≤ 8 by decide), digitValue, BitVec.toNat_ofNat,
    Nat.mod_mod] at e
  apply BitVec.eq_of_toNat_eq
  change (t.gpr .rbx).toNat = 0
  rw [Nat.add_comm] at lo
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_eq_of_lt (s.gpr .r8).isLt] at lo
  simp only [Nat.mod_mod, Nat.mod_eq_of_lt (s.gpr .r8).isLt,
    Nat.mod_eq_of_lt mi.isLt, Nat.mod_eq_of_lt (word s.mem B eN).isLt] at e lo
  exact e.trans lo

theorem headStep_ok {s : State} {B : Addr} {Z e eN k : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B e) (hp : s.gpr .rbp = off B eN)
    (he : e + 8 * k + 8 ≤ Z) (hN : eN + 64 ≤ Z) (hsep : eN + 64 ≤ e)
    (hm : readSrc s (.mem (hdr sMinv)) = some mi) :
    WP isa (AdxRotate8.headStep k) s fun t =>
      (((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ 64 * cols t = cols s + (digitValue s mi).toNat * wv s.mem B eN 8) ∧
      word t.mem B (e + 8 * k) = digitValue s mi ∧
      Outside B (e + 8 * k) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hn := hs.nowrap
  unfold AdxRotate8.headStep
  refine WP.seq (WP.mono (digit_ok hs hc he hm) fun a ⟨hd, hv, ha, ka⟩ => ?_)
  have oa : Outside B (e + 8 * k) 8 s.mem a.mem := by
    rw [ha]; exact writeW_outside _ _ _ (by omega_using [he, hn])
  refine WP.mono (core_mem (hs.congr ka.2.2) ((ka.gpr (by decide)).trans hp) hN)
    fun t ⟨ht, _, _, kt⟩ => ?_
  rw [hv, hd, oa.wv (by omega_using [hsep]) (by omega_using [hN, hn])] at ht
  refine ⟨?_, ?_, ?_, (ka.trans kt.keep).mono (by decide)⟩
  · intro hi
    have low := cancel_low hi ht
    rw [low] at ht
    simpa only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add] using ht
  · rw [kt.2.1, ha, word_writeW_self]
  · rw [kt.2.1]; exact oa
end VG.Proof.Bignum.X86_64.AdxRotate8

end

/-! ## AdxRotate8Head -/
section

/-! Eight cancellations determine a radix-512 multiplier. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem headN_ok {s : State} {B : Addr} {Z e eN n : Nat} {mi : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hc : s.gpr .rcx = off B e) (hp : s.gpr .rbp = off B eN)
    (he : e + 8 * n ≤ Z) (hN : eN + 64 ≤ Z) (hsep : eN + 64 ≤ e)
    (hh : 8 * sMinv + 8 ≤ e) (hmi : word s.mem B (8 * sMinv) = mi) :
    WP isa (AdxRotate8.headN n) s fun t =>
      (((word s.mem B eN).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
        2 ^ (64 * n) * cols t = cols s + wv t.mem B e n * wv s.mem B eN 8) ∧
      Outside B e (8 * n) s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨fun _ => by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero], Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold AdxRotate8.headN
    refine WP.seq (WP.mono (ih (by omega_using [he])) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    have ma : word a.mem B (8 * sMinv) = mi :=
      (oa.word (by omega_using [hh]) (by omega_using [hh, he, hna])).trans hmi
    have miRead : readSrc a (.mem (hdr sMinv)) = some mi := by
      rw [readSrc_word (d := 8 * sMinv) sa (by
        simp only [State.ea, hdr, (ka.gpr (by decide)).trans hdi, hdrOff]) (by omega_using [hh, he]), ma]
    refine WP.mono (headStep_ok sa ((ka.gpr (by decide)).trans hc)
      ((ka.gpr (by decide)).trans hp) (by omega_using [he]) hN hsep miRead)
      fun t ⟨vt, digit, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega_using [hsep]) (by omega_using [hN, hna])
    have mn0 : word a.mem B eN = word s.mem B eN := oa.word (by omega_using [hsep]) (by omega_using [hN, hna])
    have lo : wv t.mem B e n = wv a.mem B e n := ot.wv (by omega_using []) (by omega_using [he, hna])
    refine ⟨?_, (oa.mono (o' := e) (n' := 8 * (n + 1)) (by omega_using []) (by omega_using [])).trans
      (ot.mono (o' := e) (n' := 8 * (n + 1)) (by omega_using []) (by omega_using [])), (ka.trans kt).mono (by decide)⟩
    intro hinv
    have ea := va hinv
    have et := vt (by rw [mn0]; exact hinv)
    rw [mn] at et
    rw [wv, lo, digit, pow64_succ]
    grind
end VG.Proof.Bignum.X86_64.AdxRotate8

end
