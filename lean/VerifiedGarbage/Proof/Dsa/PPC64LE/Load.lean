module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on PPC64LE: numbers in and out of a working space

In a working space at `B` (`Env`: array 0 at `r10`, the arrays' size in
`r29`, `2 w` in `r11`, `B` in `r31`):

* `loadArr_ok`: `k` octets of a buffer apart from it, most significant
  first, into array `j`, with the array's word `w` zero;
* `storeBE_ok`: array `j`'s low `k` octets, most significant first, to a
  buffer apart from it, whose number is the array's when it is below
  `2^(8 k)` (`read_low`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- `Env`, again after a block that set `r10` back to array 0. -/
theorem env_keep10 {s t : State} {B : Addr} {Z w : Nat} {rs : List Reg} (h : Env s B Z w) (k : Keep rs s t)
    (hr : ∀ r ∈ ([.r11, .r29, .r31] : List Reg), r ∉ rs) (h10 : t.gpr .r10 = off B (slot w 0)) :
    Env t B Z w :=
  ⟨h.hs.congr k.wr, h10, (k.gpr _ (hr _ (by decide))).trans h.h29, (k.gpr _ (hr _ (by decide))).trans h.h11,
    (k.gpr _ (hr _ (by decide))).trans h.h31, h.hw, h.hw', h.hZ⟩

/-- The registers `loadArr` writes. -/
def loadRegs : List Reg := [.r0, .r10, .r14, .r15, .r16, .r17]

/-- `loadArr j`: the `k` octets at `N` (`r12`, `k` in `r6`), most significant
first, into array `j`, and the array's word `w` := 0; `r10` back to array 0. -/
theorem loadArr_ok {s : State} {B N : Addr} {Z w k j : Nat} (h : Env s B Z w) (hj : j < 28)
    (h12 : s.gpr .r12 = N) (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off N i ≠ x) :
    WP isa (loadArr j) s fun t =>
      (Mont.val32 t.mem B (slot w j) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) ∧
        word t.mem B (slot w j + 8 * w) = 0 ∧ Outside B (slot w j) (8 * (w + 1)) s.mem t.mem ∧
        t.gpr .r10 = off B (slot w 0)) ∧
      Keep loadRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZj := h.arr hj
  have hw' := h.hw'
  have hh : hdrBytes = 256 := rfl
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have ej := e j
  unfold loadArr
  refine WP.seq (WP.mono (h.base (rd := .r10) (by decide) (by decide) j) fun s₁ ⟨⟨a10, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (loadN_ok (dA := slot w j) (hs.congr k1.wr) a10
    (N := N) (by rw [k1.gpr .r12 (by decide), h12, off, BitVec.add_zero]) ((k1.gpr _ (by decide)).trans h6)
    ((k1.gpr _ (by decide)).trans h.h11) hk hkw (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [k1.rd, k1.wr]; exact hrd) (by intro i hi x hx; exact hsep i hi x hx))
    fun s₃ ⟨hv, out₃, k3⟩ => ?_)
  rw [m1] at hv out₃
  have k13 := k1.trans k3
  refine WP.mono (WP.keep [.r14, .r0, .r10] (Q := fun t =>
    t.mem = s₃.mem.writeW (off B (slot w j + 8 * w)) (0 : BitVec 64) ∧ t.gpr .r10 = off B (slot w 0))
    ?_ (by decide)) fun t ⟨⟨tm, t10⟩, k4⟩ => ⟨⟨?_, ?_, ?_, t10⟩, (k13.trans k4).mono (by decide)⟩
  · have a10' : s₃.gpr .r10 = off B (slot w j) := (k3.gpr _ (by decide)).trans a10
    have e16 : off B (slot w j + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w j + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w j + 8 * (w + 2) by omega_arith)]; congr 2
    prun [a10', (k13.gpr .r29 (by decide)).trans h.h29, (k13.gpr .r31 (by decide)).trans h.h31, off_add, e16, hh,
      BitVec.add_zero, (hs.congr k13.wr).st (show slot w j + 8 * w + 8 ≤ Z by omega_arith)]
    exact ⟨rfl, by simp [off, slot, hh]⟩
  · rw [tm, Mont.Outside.val32 (fun x hx => writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith) x hx)
      (by omega_arith) (by omega_arith)]
    exact hv
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (out₃.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside s₃.mem B (d := slot w j + 8 * w) 0 (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- The registers `storeBE` writes. -/
def storeRegs : List Reg := [.r0, .r15, .r16, .r17]

/-- `storeBE j`: array `j`'s low `k` octets (`k` in `r6`), most significant
first, to `O` (`r12`), a buffer apart from the working space. -/
theorem storeBE_ok {s : State} {B O : Addr} {Z w k j : Nat} (h : Env s B Z w) (hj : j < 28) (ho : Scr s O k)
    (h12 : s.gpr .r12 = O) (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hsep : ∀ x, ofs O x < k → Z ≤ ofs B x) :
    WP isa (storeBE j) s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem O k) = (s.mem.read (off B (slot w j)) k).toNat ∧
        Outside O 0 k s.mem t.mem) ∧ Keep storeRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hno := ho.nowrap
  have hZj := h.arr hj
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have ej := e j
  have hh : hdrBytes = 256 := rfl
  unfold storeBE
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r15) (by decide) (by decide) j) fun s₁ ⟨⟨a15, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15, .r16, .r17] (Q := fun s₂ => s₂.gpr .r15 = off B (slot w j + (k - 1)) ∧
    s₂.gpr .r16 = off O 0 ∧ s₂.gpr .r17 = BitVec.ofNat 64 k ∧ s₂.mem = s₁.mem)
    (by prun [a15, (k1.gpr .r6 (by decide)).trans h6, (k1.gpr .r12 (by decide)).trans h12, off_add,
        BitVec.add_zero]
        rw [off_sub1 _ (by omega_arith)]; congr 2; omega_arith) (by decide)) fun s₂ ⟨⟨b15, b16, b17, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r15 = off B (slot w j + (k - 1) - i) ∧ t.gpr .r16 = off O i ∧ Outside O 0 i s.mem t.mem ∧
      (∀ i' < i, t.mem (off O i') = s.mem (off B (slot w j + (k - 1 - i')))) ∧
      Keep storeRegs s t
  refine WP.mono (wp_countdown (body := .block ([.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1,
      .subi .r15 .r15 1] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := k) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨t15, t16, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b15]; rfl, b16, by rw [m2, m1]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k12.mono (by decide)⟩ b17) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have hrd : InRegions (t.rd ++ t.wr) (off B (slot w j + (k - 1) - i)) 1 := by
      rw [tk.rd, tk.wr]; exact hs.ld (show slot w j + (k - 1) - i + 1 ≤ Z by omega_arith)
    have hst : WP isa (.block [.lbz .r0 .r15 0, .stb .r0 .r16 0, .addi .r16 .r16 1,
        .subi .r15 .r15 1, .subi .r17 .r17 1]) t fun t' => t' = ((({ (t.write .r0
          ((t.mem.read (off B (slot w j + (k - 1) - i)) 1).setWidth 64)) with
          mem := t.mem.write (off O i) 1 (((t.mem.read (off B (slot w j + (k - 1) - i)) 1).setWidth 64).setWidth 8) } :
            State).write .r16 (off O (i + 1))).write .r15
              (off B (slot w j + (k - 1) - i) - BitVec.ofNat 64 1)).write .r17 (t.gpr .r17 - BitVec.ofNat 64 1) := by
      prun [t15, t16, exec_lbz' (show Reg.r15 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
        exec_stb (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), hrd,
        (ho.congr tk.wr).st (d := i) (n := 1) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem O (d := i)
      (((t.mem.read (off B (slot w j + (k - 1) - i)) 1).setWidth 64).setWidth 8) (by omega_arith)
    have harr : t.mem (off B (slot w j + (k - 1) - i)) = s.mem (off B (slot w j + (k - 1) - i)) := by
      refine tout _ (Or.inr ?_)
      by_contra hc
      have := hsep (off B (slot w j + (k - 1) - i)) (by omega_arith)
      rw [show ofs B (off B (slot w j + (k - 1) - i)) = slot w j + (k - 1) - i from
        Mem.sub_ofNat_toNat B (by omega_arith)] at this
      omega_arith
    refine ⟨⟨?_, by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; rw [off_sub1 _ (by omega_arith), show slot w j + (k - 1) - i - 1 = slot w j + (k - 1) - (i + 1) by omega_arith]
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
    · intro i' hi'
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [Bignum.PPC64LE.ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i' hi'
      · rw [write1_self, read_one', show slot w j + (k - 1 - i') = slot w j + (k - 1) - i' by omega_arith, ← harr]
    · exact tk.trans' (((((Keep.write _ _ _).trans (Keep.mem _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono
  · refine (VG.Proof.Bignum.reversed_read t.mem s.mem O (off B (slot w j)) k fun i hi => ?_).symm
    rw [off_add, tb (k - 1 - i) (by omega_arith), show k - 1 - (k - 1 - i) = i by omega_arith]

/-- The low `k` octets of a number of `2 w` digits below `2^(8 k)` are the number. -/
theorem read_low (m : Mem) (B : Addr) {d w k : Nat} (hkw : k ≤ 8 * w)
    (hlt : Mont.val32 m B d (2 * w) < 2 ^ (8 * k)) :
    (m.read (off B d) k).toNat = Mont.val32 m B d (2 * w) := by
  have e1 := VG.Proof.Bignum.read_eq_val32 m B (2 * w) d
  rw [show 4 * (2 * w) = (8 * w - k) + k by omega_arith, read_toNat_add] at e1
  have hl := (m.read (off B d) k).isLt
  generalize (m.read (off B d) k).toNat = lo at e1 hl
  generalize (m.read (off B d + BitVec.ofNat 64 k) (8 * w - k)).toNat = hi at e1
  rcases Nat.eq_zero_or_pos hi with rfl | hp
  · omega_arith
  · have := Nat.le_mul_of_pos_right (2 ^ (8 * k)) hp
    omega_arith

end VG.Proof.Dsa.PPC64LE
