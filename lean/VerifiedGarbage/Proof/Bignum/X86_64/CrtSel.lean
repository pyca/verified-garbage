import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# RSA with the CRT on x86-64: a masked copy with SSE2

`sseSelect` (`Impl/Rsa/X86_64/Crt.lean`) replaces the words of `[rbx]` by
those of `[r8]` under the mask `rbp` (all ones or zero), two words at a time
in the `xmm` registers: each pair becomes `T ^ ((E ^ T) & mask)`
(`sseSelect_ok`), over the words below `2 ⌈w / 2⌉`, one more than `w` when
`w` is odd.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## The arithmetic -/

theorem sel_mask (c : Bool) (t e : BitVec 64) : t ^^^ ((e ^^^ t) &&& mask c) = if c then e else t := by
  cases c
  · simp [mask_false]
  · rw [show mask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_comm t e, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rfl

/-- Quadword `q` of a 128-bit value. -/
abbrev q128 (v : BitVec 128) (q : Nat) : BitVec 64 := qword v q

theorem q128_low (x : BitVec 64) : q128 ((0 : BitVec 64) ++ x) 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [q128, qword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add]
  rw [BitVec.getLsbD_append]; simp [hi]

theorem q128_pair (x : BitVec 64) {q : Nat} (hq : q < 2) : q128 (x ++ x) q = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [q128, qword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]
  rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl
  · simp [hi]
  · simp [show ¬ 64 * 1 + i < 64 by omega]

theorem q128_xor (a b : BitVec 128) (q : Nat) : q128 (a ^^^ b) q = q128 a q ^^^ q128 b q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [q128, qword, hi]

theorem q128_and (a b : BitVec 128) (q : Nat) : q128 (a &&& b) q = q128 a q &&& q128 b q := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [q128, qword, hi]

/-- The mask in both quadwords: `punpcklqdq` of `movq`. -/
theorem q128_dup (x : BitVec 64) {q : Nat} (hq : q < 2) :
    q128 (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ x) ((0 : BitVec 64) ++ x)) q = x := by
  simp only [XBinOp.eval]
  rw [show qword ((0 : BitVec 64) ++ x) 0 = x from q128_low x]
  exact q128_pair x hq

/-- Quadword `q` of a 16-byte read. -/
theorem q128_read (m : Mem) (a : Addr) {q : Nat} (hq : q < 2) :
    q128 (m.readW a 128) q = m.readW (a + BitVec.ofNat 64 (8 * q)) 64 := by
  have e := readW_extract m a (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  exact e

/-- A 16-byte write, read back a quadword at a time. -/
theorem read_write128 (m : Mem) (a : Addr) (v : BitVec 128) {q : Nat} (hq : q < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * q)) 64 = q128 v q := by
  have e := readW_writeW_inside m a v (k := 8 * q) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * q) = 64 * q by omega, show 8 * 8 = 64 by rfl] at e
  exact e

/-! ## A pair of words -/

theorem off_add_eq (B : Addr) (a d : Nat) : off B a + BitVec.ofNat 64 d = off B (a + d) := off_off B a d

/-- The loop body of `sseSelect`. -/
def selPair : List Instr :=
  [.movdquLoad .xmm1 (ix .r8 .r14), .movdquLoad .xmm2 (ix .rbx .r14), .xop (.bin .pxor .xmm1 .xmm2),
    .xop (.bin .pand .xmm1 .xmm0), .xop (.bin .pxor .xmm2 .xmm1), .movdquStore (ix .rbx .r14) .xmm2,
    .alu .add .r14 (.imm 2), .alu .cmp .r14 (.reg .r13)]

theorem inRegions16 {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) {d : Nat} (hd : d + 16 ≤ Z) :
    InRegions (s.rd ++ s.wr) (off B d) 16 ∧ InRegions s.wr (off B d) 16 := by
  obtain ⟨r, hr, hc⟩ := hs.region hd (by decide)
  exact ⟨⟨r, List.mem_append_right _ hr, hc⟩, ⟨r, hr, hc⟩⟩

/-- Words `2 j` and `2 j + 1` of `[rbx]` replaced under the mask. -/
theorem selPair_ok {s : State} {B : Addr} {Z eA eo j n : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B eA)
    (hbx : s.gpr .rbx = off B eo) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2 * j))
    (h13 : s.gpr .r13 = BitVec.ofNat 64 (2 * n)) (hjn : j < n) (hn : 2 * n < 2 ^ 64)
    (hA : eA + 16 * j + 16 ≤ Z) (ho : eo + 16 * j + 16 ≤ Z) {msk : BitVec 64}
    (hx0 : ∀ q < 2, q128 (s.xmm .xmm0) q = msk) :
    WP isa (.block selPair) s fun t =>
      (∀ q < 2, word t.mem B (eo + 16 * j + 8 * q) =
        word s.mem B (eo + 16 * j + 8 * q) ^^^
          ((word s.mem B (eA + 16 * j + 8 * q) ^^^ word s.mem B (eo + 16 * j + 8 * q)) &&& msk)) ∧
      t.mem = s.mem.writeW (off B (eo + 16 * j)) (t.mem.readW (off B (eo + 16 * j)) 128) ∧
      t.gpr .r14 = BitVec.ofNat 64 (2 * (j + 1)) ∧ t.zf = some (decide (j + 1 = n)) ∧
      (∀ q < 2, q128 (t.xmm .xmm0) q = msk) ∧ Keep [.r14] s t := by
  have hn' := hs.nowrap
  obtain ⟨iA, -⟩ := inRegions16 hs (d := eA + 16 * j) (by omega)
  obtain ⟨iO, sO⟩ := inRegions16 hs (d := eo + 16 * j) (by omega)
  have eA' : s.ea (ix .r8 .r14) = off B (eA + 16 * j) := by rw [ea_ix0 s h8 h14]; congr 1; omega
  have eO' : s.ea (ix .rbx .r14) = off B (eo + 16 * j) := by rw [ea_ix0 s hbx h14]; congr 1; omega
  let X1 := s.mem.readW (off B (eA + 16 * j)) 128
  let X2 := s.mem.readW (off B (eo + 16 * j)) 128
  let s₁ := s.setXmm .xmm1 X1
  let s₂ := s₁.setXmm .xmm2 X2
  let s₃ := s₂.setXmm .xmm1 (XBinOp.eval .pxor X1 X2)
  let s₄ := s₃.setXmm .xmm1 (XBinOp.eval .pand (XBinOp.eval .pxor X1 X2) (s.xmm .xmm0))
  let V := XBinOp.eval .pxor X2 (XBinOp.eval .pand (XBinOp.eval .pxor X1 X2) (s.xmm .xmm0))
  let s₅ := s₄.setXmm .xmm2 V
  let s₆ : State := { s₅ with mem := s.mem.writeW (off B (eo + 16 * j)) V }
  unfold selPair
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [exec, eA', State.load128, iA, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, by
    simp only [exec, show s₁.ea (ix .rbx .r14) = off B (eo + 16 * j) from eO', State.load128,
      show s₁.rd = s.rd from rfl, show s₁.wr = s.wr from rfl, iO, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₃, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₄, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₅, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₆, by
    simp only [exec, show s₅.ea (ix .rbx .r14) = off B (eo + 16 * j) from eO', State.store128,
      show s₅.wr = s.wr from rfl, sO, ite_true]; rfl, ?_⟩
  have hadd : BitVec.ofNat 64 (2 * j) + 2 = BitVec.ofNat 64 (2 * (j + 1)) := by
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, BitVec.ofNat_add]; rfl
  have hcmp : (BitVec.ofNat 64 (2 * (j + 1)) - BitVec.ofNat 64 (2 * n) == 0) = decide (j + 1 = n) := by
    rw [ofNat_sub_beq (by omega) hn]; exact decide_eq_decide.mpr (by omega)
  refine WP.mono (WP.keep [.r14] (Q := fun t => t.gpr .r14 = BitVec.ofNat 64 (2 * (j + 1)) ∧
      t.zf = some (decide (j + 1 = n)) ∧ t.mem = s₆.mem ∧ t.xmm = s₆.xmm)
    (by xrun [show s₆.gpr = s.gpr from rfl, h14, h13, hadd, hcmp]; rfl) rfl) fun t ⟨⟨h14', hz, hm, hx⟩, k⟩ => ?_
  have hrd : ∀ (m : Mem) (d : Nat) {q : Nat}, q < 2 → q128 (m.readW (off B d) 128) q = word m B (d + 8 * q) :=
    fun m d q hq => by rw [q128_read m _ hq, off_add_eq]
  have hV : t.mem.readW (off B (eo + 16 * j)) 128 = V := by
    rw [hm]; exact Mem.readW_writeW_self (n := 16) _ _ V (by decide)
  refine ⟨fun q hq => ?_, by rw [hV]; exact hm, h14', hz, fun q hq => by rw [hx]; exact hx0 q hq,
    fun r hr => k.1 r hr, k.2.1, k.2.2⟩
  rw [show word t.mem B (eo + 16 * j + 8 * q) = q128 (t.mem.readW (off B (eo + 16 * j)) 128) q from
      (hrd t.mem _ hq).symm, hV]
  show q128 (X2 ^^^ ((X1 ^^^ X2) &&& s.xmm .xmm0)) q = _
  rw [q128_xor, q128_and, q128_xor, hx0 q hq, hrd _ _ hq, hrd _ _ hq]

/-! ## The selection -/

/-- `sseSelect`'s setup: the mask in both quadwords of `xmm0`, `r13 = 2 ⌈w / 2⌉`, `r14 = 0`. -/
theorem selSetup_ok {s : State} {w : Nat} (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 31) :
    WP isa (.block [.xop (.movq .xmm0 .rbp), .xop (.bin .punpcklqdq .xmm0 .xmm0), .mov .r13 (.reg .r12),
        .alu .add .r13 (.imm 1), .shift .shr .r13 1, .alu .add .r13 (.reg .r13), .mov32 .r14 (.imm 0)]) s
      fun t => (∀ q < 2, q128 (t.xmm .xmm0) q = s.gpr .rbp) ∧ t.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) ∧
        t.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧ t.mem = s.mem ∧ Keep [.r13, .r14] s t := by
  let s₂ := (s.setXmm .xmm0 ((0 : BitVec 64) ++ s.gpr .rbp)).setXmm .xmm0
    (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ s.gpr .rbp) ((0 : BitVec 64) ++ s.gpr .rbp))
  have h13 : (BitVec.ofNat 64 w + 1) >>> 1 + (BitVec.ofNat 64 w + 1) >>> 1 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) := by
    rw [ofNat_add_one]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  rw [WP.block_cons_iff]
  refine ⟨s.setXmm .xmm0 ((0 : BitVec 64) ++ s.gpr .rbp), rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨s₂, rfl, ?_⟩
  refine WP.mono (WP.keep [.r13, .r14] (Q := fun t => t.gpr .r13 = BitVec.ofNat 64 (2 * ((w + 1) / 2)) ∧
      t.gpr .r14 = BitVec.ofNat 64 (2 * 0) ∧ t.mem = s.mem ∧ t.xmm = s₂.xmm)
    (by xrun [show s₂.gpr = s.gpr from rfl, h12, h13]; exact ⟨rfl, rfl⟩) rfl) fun t ⟨⟨h13, h14, hm, hx⟩, k⟩ =>
    ⟨fun q hq => by rw [hx]; exact q128_dup _ hq, h13, h14, hm, fun r hr => k.1 r hr, k.2.1, k.2.2⟩

/-- A 16-byte write changes only its bytes. -/
theorem writeW128_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 2 ^ 64) :
    Outside base d 16 m (m.writeW (off base d) v) := by
  intro x hx
  apply Mem.write_apply (n := 16)
  simp only [ofs] at hx
  have : (x - off base d).toNat = (2 ^ 64 - d + (x - base).toNat) % 2 ^ 64 :=
    Offset.toNat_sub_add x base (by omega)
  rw [this]
  have := (x - base).isLt
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show 2 ^ 64 - d + (x - base).toNat = (x - base).toNat - d + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- After `j` pairs of `sseSelect`, of `n`. -/
structure SseInv (s : State) (B : Addr) (eA eo n : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.r13, .r14] s t
  r13 : t.gpr .r13 = BitVec.ofNat 64 (2 * n)
  r14 : t.gpr .r14 = BitVec.ofNat 64 (2 * j)
  msk : ∀ q < 2, q128 (t.xmm .xmm0) q = mask lt
  out : Outside B eo (16 * n) s.mem t.mem
  val : ∀ i < 2 * n, word t.mem B (eo + 8 * i) =
    if i < 2 * j then (if lt then word s.mem B (eA + 8 * i) else word s.mem B (eo + 8 * i))
    else word s.mem B (eo + 8 * i)

/-- `sseSelect`: `[rbx] := rbp ? [r8] : [rbx]` over `w` words, changing at most `w + 1`. -/
theorem sseSelect_ok {s : State} {B : Addr} {Z w eA eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (hbx : s.gpr .rbx = off B eo)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {lt : Bool} (hbp : s.gpr .rbp = mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 1) ≤ Z) (ho : eo + 8 * (w + 1) ≤ Z)
    (sA : eo + 8 * (w + 1) ≤ eA ∨ eA + 8 * (w + 1) ≤ eo) :
    WP isa Crt.sseSelect s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eo w) ∧
      Outside B eo (8 * (w + 1)) s.mem t.mem ∧ Keep [.r13, .r14] s t := by
  have hn := hs.nowrap
  have hnw : 16 * ((w + 1) / 2) ≤ 8 * (w + 1) := by omega
  unfold Crt.sseSelect
  refine WP.seq (WP.mono (selSetup_ok h12 hw') fun t ⟨hx, h13, h14, hm, k⟩ => ?_)
  have h0 : SseInv s B eA eo ((w + 1) / 2) lt 0 t := ⟨k, h13, h14, by rw [← hbp]; exact hx,
    by rw [hm]; exact Outside.refl _ _ _ _, fun i _ => by rw [hm]; simp⟩
  refine WP.mono (wp_upto (a := 0) (N := (w + 1) / 2) (by omega) (SseInv s B eA eo ((w + 1) / 2) lt)
    (fun j _ hj t hI => ?_) (fun t h => h) h0) fun t hI => ⟨?_, hI.out.mono (Nat.le_refl _) (by omega), hI.keep⟩
  · have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
    have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
    refine WP.mono (selPair_ok (hs.congr hI.keep.2.2) t8 tbx hI.r14 hI.r13 hj (by omega) (by omega) (by omega)
      hI.msk) fun t' ⟨hv, hm, h14, hz, hx, k⟩ => ⟨hz, ?_⟩
    have o' : Outside B (eo + 16 * j) 16 t.mem t'.mem := by rw [hm]; exact writeW128_outside _ _ _ (by omega)
    refine ⟨(hI.keep.trans k).mono (by decide), (k.gpr (by decide)).trans hI.r13, h14, hx,
      hI.out.trans (o'.mono (by omega) (by omega)), fun i hi => ?_⟩
    by_cases hlo : i < 2 * j
    · rw [o'.word (by omega) (by omega), hI.val i hi]
      simp only [hlo, show i < 2 * (j + 1) by omega, ↓reduceIte]
    by_cases hhi : 2 * j + 2 ≤ i
    · rw [o'.word (by omega) (by omega), hI.val i hi]
      simp only [hlo, show ¬ i < 2 * (j + 1) by omega, ↓reduceIte]
    obtain ⟨q, hq, rfl⟩ : ∃ q, q < 2 ∧ i = 2 * j + q := ⟨i - 2 * j, by omega, by omega⟩
    have hA' : word t.mem B (eA + 16 * j + 8 * q) = word s.mem B (eA + 16 * j + 8 * q) :=
      hI.out.word (by omega) (by omega)
    have hO' : word t.mem B (eo + 16 * j + 8 * q) = word s.mem B (eo + 16 * j + 8 * q) := by
      rw [show eo + 16 * j + 8 * q = eo + 8 * (2 * j + q) by omega, hI.val _ (by omega)]
      simp only [hlo, ↓reduceIte]
    rw [show eo + 8 * (2 * j + q) = eo + 16 * j + 8 * q by omega,
      show eA + 8 * (2 * j + q) = eA + 16 * j + 8 * q by omega, hv q hq, hA', hO', sel_mask]
    simp only [show 2 * j + q < 2 * (j + 1) by omega, ↓reduceIte]
  · cases lt
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact wv_congr fun i hi => by rw [hI.val i (by omega)]; simp
    · simp only [↓reduceIte]
      exact wv_congr2 fun i hi => by rw [hI.val i (by omega)]; simp [show i < 2 * ((w + 1) / 2) by omega]

end VG.Proof.Bignum.X86_64
