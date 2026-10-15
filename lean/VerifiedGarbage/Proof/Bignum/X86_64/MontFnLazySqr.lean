module

public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazySqr
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# `vg_rsa_lazy_mont_sqr_adx`: correctness

The head is `vg_rsa_lazy_mont_mul_adx`'s for `(o, a, a)` (`adxRest_ok`), with
`k` moved out of `r8` first (`sqrPre_ok`) and the count, `k` and `o` stored in
header words 19–21 after it (`sqrInit_ok`). Each turn of the loop is
`adxBodyLazy` (`adxBodyLazy_ok`), then `sqrNextAdx` (`sqrNext_ok`), which
points the slots of `xA` and `xB` at `o`'s array and counts; the tail is
`vg_rsa_lazy_mont_mul_adx`'s (`restore_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- `zext` and `sqrArgs`: `o`, `a`, `a` in `rdx`, `rcx`, `r8`, and `k` in `r9`. -/
theorem sqrPre_ok {s : State} {o a k : Nat} (ho : o < 8) (ha : a < 8) (hk : k < 2 ^ 32)
    (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o) (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a)
    (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 k) :
    WP isa (.block (zext ++ sqrArgs)) s fun t =>
      t.gpr .rdx = BitVec.ofNat 64 o ∧ t.gpr .rcx = BitVec.ofNat 64 a ∧ t.gpr .r8 = BitVec.ofNat 64 a ∧
      t.gpr .r9 = BitVec.ofNat 64 k ∧ t.mem = s.mem ∧ t.xmm = s.xmm ∧ Keep [.rdx, .rcx, .r8, .r9] s t := by
  refine WP.mono (WP.keep [.rdx, .rcx, .r8, .r9] (c := .block (zext ++ sqrArgs))
    (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 o ∧ t.gpr .rcx = BitVec.ofNat 64 a ∧ t.gpr .r8 = BitVec.ofNat 64 a ∧
      t.gpr .r9 = BitVec.ofNat 64 k ∧ t.mem = s.mem ∧ t.xmm = s.xmm) ?_ rfl)
    fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, kt⟩
  unfold zext sqrArgs
  simp only [List.cons_append, List.nil_append]
  xrun [hdx, hcx, h8, setWidth_ofNat32 (show o < 2 ^ 32 by omega_arith), setWidth_ofNat32 (show a < 2 ^ 32 by omega_arith),
    setWidth_ofNat32 hk, setReg_xmm]

/-- The memory `sqrInit` leaves: the count 0, `k` and `o` in header words 19–21. -/
def initMem (m : Mem) (B : Addr) (o k : Nat) : Mem :=
  ((m.writeW (off B (8 * sFn 3)) 0#64).writeW (off B (8 * sFn 4)) (BitVec.ofNat 64 k)).writeW
    (off B (8 * sFn 5)) (BitVec.ofNat 64 o)

theorem sqrInit_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot w 8 ≤ Z) {o k : Nat} (hdx : s.gpr .rdx = BitVec.ofNat 64 o) (h9 : s.gpr .r9 = BitVec.ofNat 64 k) :
    WP isa (.block sqrInit) s fun t => t.mem = initMem s.mem B o k ∧ t.xmm = s.xmm ∧ Keep [.rax] s t := by
  have hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rax] (c := .block sqrInit)
    (Q := fun t => t.mem = initMem s.mem B o k ∧ t.xmm = s.xmm) ?_ rfl) fun t ⟨h, kt⟩ => ⟨h.1, h.2, kt⟩
  unfold sqrInit initMem
  xrun [State.ea, hdr, hdi, hdx, h9, hdrOff, hw (sFn 3) (by decide), hw (sFn 4) (by decide), hw (sFn 5) (by decide),
    setReg_xmm]
  rfl

/-- The memory `sqrNextAdx` leaves: the slots of `xA` and `xB` at `o`'s array,
and the count `j + 1`. -/
def nextMem (m : Mem) (B : Addr) (w o j : Nat) : Mem :=
  ((m.writeW (off B (8 * sArr xA)) (off B (slot w o))).writeW (off B (8 * sArr xB)) (off B (slot w o))).writeW
    (off B (8 * sFn 3)) (BitVec.ofNat 64 (j + 1))

theorem sqrNext_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : slot w 8 ≤ Z) {o j k : Nat} (hj : j + 1 < 2 ^ 64) (hk : k < 2 ^ 64)
    (hO : word s.mem B (8 * sArr xO) = off B (slot w o)) (h5 : word s.mem B (8 * sFn 5) = BitVec.ofNat 64 o)
    (h3 : word s.mem B (8 * sFn 3) = BitVec.ofNat 64 j) (h4 : word s.mem B (8 * sFn 4) = BitVec.ofNat 64 k) :
    WP isa (.block sqrNextAdx) s fun t =>
      t.mem = nextMem s.mem B w o j ∧ t.gpr .rdx = BitVec.ofNat 64 o ∧ t.gpr .rcx = BitVec.ofNat 64 o ∧
      t.gpr .r8 = BitVec.ofNat 64 o ∧ t.zf = some (decide (j + 1 = k)) ∧ t.xmm = s.xmm ∧
      Keep [.rax, .rdx, .rcx, .r8] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  have hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hs.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r8] (c := .block sqrNextAdx)
    (Q := fun t => t.mem = nextMem s.mem B w o j ∧ t.gpr .rdx = BitVec.ofNat 64 o ∧ t.gpr .rcx = BitVec.ofNat 64 o ∧
      t.gpr .r8 = BitVec.ofNat 64 o ∧ t.zf = some (decide (j + 1 = k)) ∧ t.xmm = s.xmm) ?_ rfl)
    fun t ⟨h, kt⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, kt⟩
  unfold sqrNextAdx sqrCount nextMem
  simp only [List.cons_append, List.nil_append]
  have e3 : word (((s.mem.writeW (off B (8 * sArr xA)) (off B (slot w o))).writeW (off B (8 * sArr xB))
      (off B (slot w o)))) B (8 * sFn 3) = BitVec.ofNat 64 j :=
    word_skip (word_skip h3 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
  have e5 : word (((s.mem.writeW (off B (8 * sArr xA)) (off B (slot w o))).writeW (off B (8 * sArr xB))
      (off B (slot w o)))) B (8 * sFn 5) = BitVec.ofNat 64 o :=
    word_skip (word_skip h5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
  have e4 : word ((((s.mem.writeW (off B (8 * sArr xA)) (off B (slot w o))).writeW (off B (8 * sArr xB))
      (off B (slot w o)))).writeW (off B (8 * sFn 3)) (BitVec.ofNat 64 (j + 1))) B (8 * sFn 4) = BitVec.ofNat 64 k :=
    word_skip (word_skip (word_skip h4 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide))
      (by decide) (by decide) (by decide)
  unfold word at hO e3 e4 e5
  xrun [State.ea, hdr, hdi, hdrOff, hl (sArr xO) (by decide), hl (sFn 3) (by decide), hl (sFn 4) (by decide),
    hl (sFn 5) (by decide), hw (sArr xA) (by decide), hw (sArr xB) (by decide), hw (sFn 3) (by decide), hO, e3, e4, e5,
    ofNat_add_one, ofNat_sub_beq hj hk, setReg_xmm, RegUpd.xmm_setFlags, RegUpd.xmm_setReg]

/-! ## The value after each squaring -/

/-- One more squaring: from `y R ≡ x²` and `x R^(2^j - 1) ≡ A^(2^j)`,
`y R^(2^(j+1) - 1) ≡ A^(2^(j+1))`. -/
theorem sqr_iter_step {M R x y A j : Nat} (hy : y * R % M = x * x % M)
    (hx : x * R ^ (2 ^ j - 1) % M = A ^ 2 ^ j % M) : y * R ^ (2 ^ (j + 1) - 1) % M = A ^ 2 ^ (j + 1) % M := by
  have e : 2 ^ (j + 1) - 1 = 1 + (2 ^ j - 1) + (2 ^ j - 1) := by
    have := Nat.one_le_two_pow (n := j); rw [Nat.pow_succ]; omega
  have hA : A ^ 2 ^ (j + 1) = A ^ 2 ^ j * A ^ 2 ^ j := by
    rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]
  rw [e, Nat.pow_add, Nat.pow_add, Nat.pow_one, hA]
  generalize R ^ (2 ^ j - 1) = T at hx ⊢
  calc y * (R * T * T) % M = (y * R) * (T * T) % M := by rw [Nat.mul_assoc R, ← Nat.mul_assoc]
    _ = (y * R % M) * (T * T % M) % M := Nat.mul_mod _ _ _
    _ = (x * x % M) * (T * T % M) % M := by rw [hy]
    _ = (x * T) * (x * T) % M := by rw [← Nat.mul_mod]; congr 1; grind
    _ = (x * T % M) * (x * T % M) % M := Nat.mul_mod _ _ _
    _ = (A ^ 2 ^ j % M) * (A ^ 2 ^ j % M) % M := by rw [hx]
    _ = A ^ 2 ^ j * A ^ 2 ^ j % M := (Nat.mul_mod _ _ _).symm

/-! ## The loop's invariant -/

/-- The array squared next: `a`, then `o`. -/
def cur (a o j : Nat) : Nat := if j = 0 then a else o

/-- What the function may change while the loop runs: header words 16–21 and
28–31, and the arrays `aAcc`, `aTmp` and `o`. -/
def sqrRanges (w o : Nat) : List (Nat × Nat) :=
  [(8 * sFn 0, 48), (8 * sFn 12, 32), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w o, 8 * (w + 2))]

/-- After `j` squarings, from the state `s` at the call. -/
structure SqrInv (s t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (o a k j : Nat) : Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  hdr : Hdr t.mem B w minv
  rdx : t.gpr .rdx = BitVec.ofNat 64 o
  rcx : t.gpr .rcx = BitVec.ofNat 64 (cur a o j)
  r8 : t.gpr .r8 = BitVec.ofNat 64 (cur a o j)
  ops : Ops t.mem B w (adxOps o (cur a o j) (cur a o j))
  cnt : word t.mem B (8 * sFn 3) = BitVec.ofNat 64 j
  kk : word t.mem B (8 * sFn 4) = BitVec.ofNat 64 k
  oo : word t.mem B (8 * sFn 5) = BitVec.ofNat 64 o
  frm : Frm B (sqrRanges w o) s.mem t.mem
  sv : Saved s t
  x3 : t.xmm .xmm3 = s.mem.readW (off B (8 * sFn 0)) 128
  x4 : t.xmm .xmm4 = s.mem.readW (off B (8 * sFn 2)) 128
  x5 : t.xmm .xmm5 = s.mem.readW (off B (8 * sFn 4)) 128
  x6 : t.xmm .xmm6 = s.mem.readW (off B (8 * sFn 12)) 128
  x7 : t.xmm .xmm7 = s.mem.readW (off B (8 * sFn 14)) 128
  val : wv t.mem B (slot w (cur a o j)) w * (2 ^ (64 * w)) ^ (2 ^ j - 1) % wv s.mem B (slot w aN) w =
    wv s.mem B (slot w a) w ^ 2 ^ j % wv s.mem B (slot w aN) w

/-- The head: `zext`, `sqrArgs`, `vg_rsa_lazy_mont_mul_adx`'s `saves` and
`slotsIn` for `(o, a, a)`, and `sqrInit`. -/
theorem sqrHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o a k : Nat}
    (ho : o < 8) (ha : a < 8) (hk : k < 2 ^ 32) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 k) :
    WP isa (.block (zext ++ sqrArgs ++ saves ++ slotsIn ++ sqrInit)) s fun t =>
      SqrInv s t B Z w minv o a k 0 ∧ Keep [.rdx, .rcx, .r8, .r9, .rax] s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have s0 : ∀ j, slot w 0 ≤ slot w j := fun j => by unfold slot; omega_arith
  have h256 : 8 * sFn 0 + 48 ≤ slot w 0 := by unfold sFn slot hdrBytes; omega_arith
  rw [show zext ++ sqrArgs ++ saves ++ slotsIn ++ sqrInit = (zext ++ sqrArgs) ++ ((saves ++ slotsIn) ++ sqrInit) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono (sqrPre_ok ho ha hk hdx hcx h8) fun s₁ ⟨d1, c1, r1, n1, m1, _, k1⟩ => ?_
  rw [WP.block_append_iff]
  have hs₁ := hs.congr k1.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k1.gpr (by decide)).trans hdi
  refine WP.mono (adxRest_ok hs₁ hdi₁ (m1 ▸ hH) hZ ho ha ha d1 c1 r1)
    fun s₂ ⟨m2, k2, sv2, x3, x4, x5, x6, x7⟩ => ?_
  have hs₂ := hs₁.congr k2.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k2.gpr (by decide)).trans hdi₁
  refine WP.mono (sqrInit_ok hs₂ hdi₂ hZ ((k2.gpr (by decide)).trans d1) ((k2.gpr (by decide)).trans n1))
    fun t ⟨m3, xt, k3⟩ => ?_
  rw [m1] at m2 x3 x4 x5 x6 x7
  rw [m2] at m3
  have kt := (k1.trans k2).trans k3
  -- The head's memory: header words 16–21 only.
  have oH : Outside B (8 * sFn 0) 48 s.mem (headMem s.mem B w o a a) :=
    (headMem_outside s.mem B w o a a).mono (by decide) (by decide)
  have oI : Outside B (8 * sFn 0) 48 (headMem s.mem B w o a a) t.mem := by
    rw [m3]; unfold initMem
    exact (((writeW_outside _ B _ (by unfold sFn; omega_arith)).mono (by decide) (by decide)).trans
      ((writeW_outside _ B _ (by unfold sFn; omega_arith)).mono (by decide) (by decide))).trans
      ((writeW_outside _ B _ (by unfold sFn; omega_arith)).mono (by decide) (by decide))
  have oT := oH.trans oI
  have hops := headMem_ops s.mem B w o a a
  refine ⟨⟨hs.congr kt.2.2, (kt.gpr (by decide)).trans hdi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    Frm.of_outside oT (by simp [sqrRanges]), (sv2.of_keep k1 (by decide)).of_xmm xt,
    by rw [xt]; exact x3, by rw [xt]; exact x4, by rw [xt]; exact x5, by rw [xt]; exact x6, by rw [xt]; exact x7, ?_⟩,
    kt.mono (by decide)⟩
  · rw [m3]; unfold initMem
    exact (((headMem_hdr hH o a a).store (i := sFn 3) (by decide) (by decide) _).store (i := sFn 4) (by decide)
      (by decide) _).store (i := sFn 5) (by decide) (by decide) _
  · exact ((k3.gpr (by decide)).trans (k2.gpr (by decide))).trans d1
  · simp only [cur, ↓reduceIte]; exact ((k3.gpr (by decide)).trans (k2.gpr (by decide))).trans c1
  · simp only [cur, ↓reduceIte]; exact ((k3.gpr (by decide)).trans (k2.gpr (by decide))).trans r1
  · simp only [cur, ↓reduceIte]
    intro p hp
    obtain ⟨hlt, hat⟩ := hops p hp
    refine ⟨hlt, hat.of_word ?_⟩
    simp only [adxOps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [m3]; unfold initMem
    rcases hp with rfl | rfl | rfl <;> dsimp only <;>
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
  · rw [m3]; unfold initMem
    exact word_skip (word_skip (word_writeW_self _ _ _ _) (by decide) (by decide) (by decide)) (by decide) (by decide)
      (by decide)
  · rw [m3]; unfold initMem
    exact word_skip (word_writeW_self _ _ _ _) (by decide) (by decide) (by decide)
  · rw [m3]; unfold initMem; exact word_writeW_self _ _ _ _
  · simp only [cur, ↓reduceIte, Nat.pow_zero, Nat.sub_self, Nat.mul_one, Nat.pow_one]
    rw [oT.wv (by have := s0 a; omega_arith) (by have := sl a ha; omega_arith)]

/-- An array the loop does not change keeps its value. -/
theorem sqrRanges_wv {B : Addr} {w o j : Nat} {m m' : Mem} (h : Frm B (sqrRanges w o) m m') (hj : j < 8)
    (h2 : j ≠ aAcc) (h3 : j ≠ aTmp) (h4 : j ≠ o) (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    wv m' B (slot w j) w = wv m B (slot w j) w := by
  have h0 : 8 * sFn 12 + 32 ≤ slot w j := by unfold sFn slot hdrBytes; omega_arith
  refine h.wv_eq (fun r hr => ?_) (by have := slot_le (w := w) hj; omega_arith)
  simp only [sqrRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · right; unfold sFn at *; omega_arith
  · right; exact h0
  · have := slot_sep (w := w) h2; omega_arith
  · have := slot_sep (w := w) h3; omega_arith
  · have := slot_sep (w := w) h4; omega_arith

theorem sqrRanges_word {B : Addr} {w o j : Nat} {m m' : Mem} (h : Frm B (sqrRanges w o) m m') (hj : j < 8)
    (h2 : j ≠ aAcc) (h3 : j ≠ aTmp) (h4 : j ≠ o) (hn : B.toNat + slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) :
    word m' B (slot w j) = word m B (slot w j) := by
  have h0 : 8 * sFn 12 + 32 ≤ slot w j := by unfold sFn slot hdrBytes; omega_arith
  refine h.word_eq (fun r hr => ?_) (by have := slot_le (w := w) hj; omega_arith)
  simp only [sqrRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · right; unfold sFn at *; omega_arith
  · right; exact h0
  · have := slot_sep (w := w) h2; omega_arith
  · have := slot_sep (w := w) h3; omega_arith
  · have := slot_sep (w := w) h4; omega_arith

/-- The header after a squaring: words below 28 as before. -/
theorem body_hdr_word {B : Addr} {w o : Nat} {m mb m' : Mem} (omb : Outside B (8 * sFn 12) 32 m mb)
    (har : Arrays B w [aAcc, aTmp, o] mb m') {i : Nat} (hi : i < 28) : word m' B (8 * i) = word m B (8 * i) :=
  (har.hslot (by omega)).trans (omb.word (by unfold sFn; omega) (by omega))

/-- The memory `sqrNextAdx` leaves: header words 17–19 only. -/
theorem nextMem_outside (m : Mem) (B : Addr) (w o j : Nat) : Outside B (8 * sFn 0) 48 m (nextMem m B w o j) := by
  unfold nextMem
  exact (((writeW_outside _ B _ (by unfold sArr xA; omega_arith)).mono (by decide) (by decide)).trans
    ((writeW_outside _ B _ (by unfold sArr xB; omega_arith)).mono (by decide) (by decide))).trans
    ((writeW_outside _ B _ (by unfold sFn; omega_arith)).mono (by decide) (by decide))

/-- A turn of the loop: a squaring of the array `cur a o j` into `o`
(`adxBodyLazy_ok`), then `sqrNextAdx`. -/
theorem sqrStep_ok {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {o a k j : Nat}
    (I : SqrInv s t B Z w minv o a k j) (hj : j < k) (hk : k < 2 ^ 32) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ho0 : o ≠ aN)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.seq adxBodyLazy (.block sqrNextAdx)) t fun t' =>
      t'.zf = some (decide (j + 1 = k)) ∧ SqrInv s t' B Z w minv o a k (j + 1) ∧ Keep mmRegs t t' := by
  have hn := I.scr.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have s0 : ∀ j, slot w 0 ≤ slot w j := fun j => by unfold slot; omega_arith
  have h256 : 8 * sFn 0 + 48 ≤ slot w 0 := by unfold sFn slot hdrBytes; omega_arith
  have hc : cur a o j < 8 := by unfold cur; split <;> assumption
  have hc1 : cur a o j ≠ aAcc := by unfold cur; split <;> assumption
  have hc2 : cur a o j ≠ aTmp := by unfold cur; split <;> assumption
  have hZn : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  have hM : wv t.mem B (slot w aN) w = wv s.mem B (slot w aN) w :=
    sqrRanges_wv I.frm (by decide) (by decide) (by decide) (Ne.symm ho0) hZn
  have hinvT : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [sqrRanges_word I.frm (by decide) (by decide) (by decide) (Ne.symm ho0) hZn (by omega_arith)]; exact hinv
  refine WP.seq (WP.mono (WP.vecKeep (by decide) (adxBodyLazy_ok I.scr I.rdi I.hdr hZ hw hw' ho hc hc ho1 ho2 hc1
    hc2 hc1 hc2 I.ops I.rdx I.rcx I.r8 hinvT)) fun t₁ ⟨⟨heq, ⟨mb, omb, har⟩, k₁⟩, hx₁, _⟩ => ?_)
  have hs₁ := I.scr.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans I.rdi
  have hw1 : ∀ i < 28, word t₁.mem B (8 * i) = word t.mem B (8 * i) := fun i hi => body_hdr_word omb har hi
  have hO₁ : word t₁.mem B (8 * sArr xO) = off B (slot w o) := (hw1 _ (by decide)).trans (I.ops.at (mem_adxOps_o _ _ _))
  refine WP.mono (sqrNext_ok hs₁ hdi₁ hZ (j := j) (k := k) (by omega) (by omega) hO₁ ((hw1 _ (by decide)).trans I.oo)
    ((hw1 _ (by decide)).trans I.cnt) ((hw1 _ (by decide)).trans I.kk)) fun t₂ ⟨m2, d2, c2, r2, z2, x2, k2⟩ => ?_
  have kt := k₁.trans k2
  have hcur : cur a o (j + 1) = o := by simp [cur]
  have oN : Outside B (8 * sFn 0) 48 t₁.mem t₂.mem := m2 ▸ nextMem_outside t₁.mem B w o j
  have hH₁ : Hdr t₁.mem B w minv :=
    ⟨(hw1 _ (by decide)).trans I.hdr.hw, (hw1 _ (by decide)).trans I.hdr.hminv,
      fun i hi => (hw1 _ (by unfold sArr; omega)).trans (I.hdr.harr i hi)⟩
  refine ⟨z2, ⟨I.scr.congr kt.2.2, (kt.gpr (by decide)).trans I.rdi, ?_, d2, hcur ▸ c2, hcur ▸ r2, ?_, ?_, ?_, ?_,
    ?_, I.sv.of_xmm (x2.trans hx₁), ?_, ?_, ?_, ?_, ?_, ?_⟩, kt.mono (by decide)⟩
  · rw [m2]; unfold nextMem
    exact ((hH₁.store (i := sArr xA) (by decide) (by decide) _).store (i := sArr xB) (by decide) (by decide) _).store
      (i := sFn 3) (by decide) (by decide) _
  · rw [hcur]
    intro p hp
    simp only [adxOps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [m2]; unfold nextMem
    rcases hp with rfl | rfl | rfl <;> dsimp only
    · refine ⟨by decide, ?_⟩
      unfold OpAt
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
      exact hO₁
    · refine ⟨by decide, ?_⟩
      unfold OpAt
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
      exact word_writeW_self _ _ _ _
    · refine ⟨by decide, ?_⟩
      unfold OpAt
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
      exact word_writeW_self _ _ _ _
  · rw [m2]; unfold nextMem; exact word_writeW_self _ _ _ _
  · rw [m2]; unfold nextMem
    exact word_skip (word_skip (word_skip ((hw1 _ (by decide)).trans I.kk) (by decide) (by decide) (by decide))
      (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
  · rw [m2]; unfold nextMem
    exact word_skip (word_skip (word_skip ((hw1 _ (by decide)).trans I.oo) (by decide) (by decide) (by decide))
      (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
  · have f1 : Frm B (sqrRanges w o) t.mem t₁.mem := fun x hx => by
      refine (har x fun j hj => ?_).trans (omb x (hx (8 * sFn 12, 32) (by simp [sqrRanges])))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      exact hx (slot w j, 8 * (w + 2)) (by rcases hj with h | h | h <;> simp [sqrRanges, h])
    have f2 : Frm B (sqrRanges w o) t₁.mem t₂.mem := Frm.of_outside oN (by simp [sqrRanges])
    exact (I.frm.trans f1).trans f2
  · rw [x2, hx₁]; exact I.x3
  · rw [x2, hx₁]; exact I.x4
  · rw [x2, hx₁]; exact I.x5
  · rw [x2, hx₁]; exact I.x6
  · rw [x2, hx₁]; exact I.x7
  · rw [hcur, oN.wv (by have := s0 o; omega_arith) (by have := sl o ho; omega_arith)]
    rw [hM] at heq
    exact sqr_iter_step heq I.val

/-- `vg_rsa_lazy_mont_sqr_adx`'s code: `k ≥ 1` lazy squarings of `[a]` into `[o]`. -/
theorem sqrAdxLazy_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a k : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ho0 : o ≠ aN) (ha1 : a ≠ aAcc)
    (ha2 : a ≠ aTmp) (hk1 : 1 ≤ k) (hk : k < 2 ^ 32) (hdx : (s.gpr .rdx).setWidth 32 = BitVec.ofNat 32 o)
    (hcx : (s.gpr .rcx).setWidth 32 = BitVec.ofNat 32 a) (h8 : (s.gpr .r8).setWidth 32 = BitVec.ofNat 32 k)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa sqrAdxLazy s fun t =>
      wv t.mem B (slot w o) w * (2 ^ (64 * w)) ^ (2 ^ k - 1) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w ^ 2 ^ k % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t ∧
      ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15], t.gpr r = s.gpr r := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have s0 : ∀ j, slot w 0 ≤ slot w j := fun j => by unfold slot; omega_arith
  have h256 : 8 * sFn 12 + 32 ≤ slot w 0 := by unfold sFn slot hdrBytes; omega_arith
  have hZ32 : 8 * 32 ≤ Z := by have := hdr_lt_slot w 0 (show 31 < 32 by decide); have := sl 0 (by decide); omega_arith
  unfold sqrAdxLazy
  refine WP.seq (WP.mono (sqrHead_ok hs hdi hH hZ ho ha hk hdx hcx h8) fun t₀ ⟨I₀, k₀⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := k) (by omega)
    (fun j t => SqrInv s t B Z w minv o a k j ∧ Keep mmRegs s t)
    (Q := fun t => SqrInv s t B Z w minv o a k k ∧ Keep mmRegs s t)
    (fun j _ hjk t ⟨I, kt⟩ => WP.mono (sqrStep_ok I hjk hk hZ hw hw' ho ha ho1 ho2 ho0 ha1 ha2 hinv)
      fun t' ⟨hz, I', k'⟩ => ⟨hz, I', kt.trans k' |>.mono (by decide)⟩)
    (fun _ h => h) ⟨I₀, k₀.mono (by decide)⟩) fun t ⟨I, kt⟩ => ?_)
  refine WP.mono (restore_ok I.scr I.rdi hZ32 (m₀ := s.mem) I.x3 I.x4 I.x5 I.x6 I.x7 I.sv)
    fun t' ⟨rs, o₃, in₃, inb₃, k₃⟩ => ?_
  have hcur : cur a o k = o := by simp [cur]; omega
  have hval := I.val
  rw [hcur] at hval
  have hvo : wv t'.mem B (slot w o) w = wv t.mem B (slot w o) w :=
    o₃.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> have := s0 o <;> unfold sFn slot hdrBytes at * <;> omega_arith)
      (by have := sl o ho; omega_arith)
  refine ⟨by rw [hvo]; exact hval, fun x hx => ?_, (kt.trans k₃).mono (by decide), rs⟩
  by_cases hr : 8 * sFn 0 ≤ ofs B x ∧ ofs B x < 8 * sFn 0 + 48
  · exact in₃ x hr.1 hr.2
  by_cases hb : 8 * sFn 12 ≤ ofs B x ∧ ofs B x < 8 * sFn 12 + 32
  · exact inb₃ x hb.1 hb.2
  rw [o₃ x (fun r hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl <;> simp only [] <;> omega_arith)]
  refine I.frm x fun r hr' => ?_
  simp only [sqrRanges, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl
  · simp only []; omega_arith
  · simp only []; omega_arith
  · exact hx aAcc (by simp)
  · exact hx aTmp (by simp)
  · exact hx o (by simp)

end VG.Proof.Bignum.X86_64
