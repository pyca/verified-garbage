module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Twos
public import VerifiedGarbage.Proof.Bignum.ShiftStages
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
import VerifiedGarbage.Proof.Rsa.X86_64.WordInit
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the pieces of the shifts by stages

A stage's test leaves its mask `keep` in `sB2` (`keepOf_ok`, `testW_ok`,
`testB_ok`); a shift by whole words or by bits writes a temporary
(`shrWords_ok`, `shlWords_ok`, `shrClB_ok`, `shlClB_ok`), which `selK_ok`
selects where `keep` is clear.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `keepOf`: `sB2 := ` the mask of `rbp ≠ 0`. -/
theorem keepOf_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {z : Prop} [Decidable z]
    (hz : s.gpr .rbp = 0 ↔ z) :
    WP isa (.block keepOf) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sB2)) (mask (!decide z)) ∧ Keep [.rbp] s t := by
  have hst := h.scr.st (d := 8 * sB2) (by have := h.h256; unfold sB2 sFn; omega_arith)
  have e : decide (s.gpr .rbp = 0) = decide z := by
    by_cases hz' : z
    · rw [decide_eq_true hz', decide_eq_true (hz.mpr hz')]
    · rw [decide_eq_false hz', decide_eq_false (fun h => hz' (hz.mp h))]
  refine WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sB2)) (mask (!decide z))) ?_ rfl
  unfold keepOf
  xrun [State.ea, hdr, h.rdi, hdrOff, hst, decide_lt_one', e, sx_m1]
  rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide z))) = mask (decide z) from rfl, mask_xor1]

/-- `selK wd j t`: `[j] := keep ? [j] : [t]` over `w` words, or `2 w + 2` if `wd`. -/
theorem selK_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (wd : Bool) {j t : Nat}
    (hj : j + (if wd then 2 else 1) ≤ 16) (ht : t + (if wd then 2 else 1) ≤ 16)
    (hjt : slot w j + 8 * shlN wd w ≤ slot w t ∨ slot w t + 8 * shlN wd w ≤ slot w j) {keep : Bool}
    (hk : word s.mem B (8 * sB2) = mask keep) :
    WP isa (selK wd j t) s fun s' =>
      wv s'.mem B (slot w j) (shlN wd w) =
        (if keep then wv s.mem B (slot w j) (shlN wd w) else wv s.mem B (slot w t) (shlN wd w)) ∧
      Outside B (slot w j) (8 * shlN wd w) s.mem s'.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rbp, .rax, .rdx, .r14] s s' := by
  unfold selK wsW
  exact selPre_ok h wd hj ht hjt (maskLd (by decide) h.h256 hk)

theorem setW32 {c : Nat} (hc : c < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 c) = BitVec.ofNat 64 c :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_arith)

/-- `testW`'s setup: the bases of `u` and `x₂`, `rbp := 0` and `c`. -/
theorem testHd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat} (hc : c < 2 ^ 32) :
    WP isa (.block (ws ++ base 7 .rbx ++ base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))) s fun t =>
      t.gpr .rbx = off B (slot w 7) ∧ t.gpr .r10 = off B (slot w 6) ∧ t.gpr .rbp = 0 ∧
        t.gpr .r12 = BitVec.ofNat 64 c ∧ t.mem = s.mem ∧ Keep [.r12, .r9, .rbx, .r10, .rbp] s t := by
  rw [show ws ++ base 7 .rbx ++ base 6 .r10 ++ ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) = ws ++ ((base 7 .rbx ++ base 6 .r10) ++ ([.mov32 .rbp (.imm 0),
      .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)) by simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok 7 6 (r₁ := .rbx) (r₂ := .r10) (w := w) (by decide) (by decide)
      (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hbx, h10, m₂, k₂⟩ => ?_
  refine WP.mono (WP.keep [.rbp, .r12] (Q := fun t => t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 c ∧
    t.mem = s₂.mem) (by xrun [setW32 hc]) rfl) fun t ⟨⟨hbp, h12', m₃⟩, k₃⟩ => ?_
  exact ⟨(k₃.gpr (by decide)).trans hbx, (k₃.gpr (by decide)).trans h10, hbp, h12', by rw [m₃, m₂, m₁],
    ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `testW both c`: `sB2 := ` the mask of the low `c` words of `u` (array 7),
and of `x₂` (array 6) if `both`, not all zero. -/
theorem testW_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (both : Bool) {c : Nat}
    (hc : 1 ≤ c) (hcw : c ≤ w) :
    WP isa (seqs (testW both c)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sB2))
        (mask (!decide (wv s.mem B (slot w 7) c = 0 ∧ (both = true → wv s.mem B (slot w 6) c = 0)))) ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have s7 := h.sl (j := 7) (by decide)
  have s6 := h.sl (j := 6) (by decide)
  have hw2 := h.w2
  simp only [testW, seqs]
  refine WP.seq (WP.seq (WP.mono (testHd_ok h (c := c) (by omega_arith)) fun s₁ ⟨hbx, h10, hbp, h12, m₁, k₁⟩ => ?_))
  have hs := h.scr.congr k₁.2.2
  have h₁ : Ws s₁ B Z w := h.congrP (P := fun _ => False) (fun _ _ => by rw [m₁]) (fun _ f => f.elim) k₁ (by simp)
  cases both
  · refine WP.mono (or1_ok hs hbx h12 hc (by omega_arith) (by omega_arith)) fun s₂ ⟨hz, m₂, k₂⟩ => ?_
    refine WP.mono (keepOf_ok (h₁.congrP (P := fun _ => False) (fun _ _ => by rw [m₂]) (fun _ f => f.elim) k₂ (by simp))
      (z := wv s.mem B (slot w 7) c = 0 ∧ (false = true → wv s.mem B (slot w 6) c = 0))
      (by rw [hz, hbp, m₁]; simp)) fun t ⟨m₃, k₃⟩ => ?_
    exact ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  · refine WP.mono (or2_ok hs hbx h10 h12 hc (by omega_arith) (by omega_arith) (by omega_arith))
      fun s₂ ⟨hz, m₂, k₂⟩ => ?_
    refine WP.mono (keepOf_ok (h₁.congrP (P := fun _ => False) (fun _ _ => by rw [m₂]) (fun _ f => f.elim) k₂ (by simp))
      (z := wv s.mem B (slot w 7) c = 0 ∧ (true = true → wv s.mem B (slot w 6) c = 0))
      (by rw [hz, hbp, m₁]; simp)) fun t ⟨m₃, k₃⟩ => ?_
    exact ⟨by rw [m₃, m₂, m₁], ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- A word shifted left by `64 - b` is zero exactly when its low `b` bits are. -/
theorem shl_zero_iff (y : BitVec 64) {b : Nat} (hb : b ≤ 64) : y <<< (64 - b) = 0 ↔ y.toNat % 2 ^ b = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_shiftLeft, show (0 : BitVec 64).toNat = 0 from rfl, Nat.shiftLeft_eq]
  have hp : 2 ^ b * 2 ^ (64 - b) = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega_using [hb]
  rw [← hp, Nat.mul_mod_mul_right]
  constructor
  · intro h0
    rcases Nat.mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h (Nat.ne_of_gt (Nat.two_pow_pos _))
  · intro h0; rw [h0, Nat.zero_mul]

/-- `testB both b`: `sB2 := ` the mask of the low `b` bits of `u`'s low word,
and of `x₂`'s if `both`, not all zero. -/
theorem testB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (both : Bool) {b : Nat}
    (hb : 1 ≤ b) (hb' : b ≤ 32) :
    WP isa (seqs (testB both b)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sB2))
        (mask (!decide ((word s.mem B (slot w 7)).toNat % 2 ^ b = 0 ∧
          (both = true → (word s.mem B (slot w 6)).toNat % 2 ^ b = 0)))) ∧
      Keep [.r12, .r9, .rbx, .r10, .rbp, .rax] s t := by
  have hn := h.scr.nowrap
  have s7 := h.sl (j := 7) (by decide)
  have s6 := h.sl (j := 6) (by decide)
  simp only [testB, seqs]
  rw [show ws ++ base 7 .rbx ++ base 6 .r10 ++ ([.mov .rax (.mem (at0 .rbx))] : List Instr) ++
      (if both = true then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      ([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf =
    ws ++ ((base 7 .rbx ++ base 6 .r10) ++ ((([.mov .rax (.mem (at0 .rbx))] : List Instr) ++
      (if both = true then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      ([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr)) ++ keepOf)) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok 7 6 (r₁ := .rbx) (r₂ := .r10) (w := w) (by decide) (by decide)
      (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hbx, h10, m₂, k₂⟩ => ?_
  have hs := h.scr.congr (k₁.trans k₂).2.2
  rw [WP.block_append_iff]
  have hz : ∀ t : State, t.gpr .rbp = (word s.mem B (slot w 7) |||
      (if both then word s.mem B (slot w 6) else 0)) <<< (64 - b) → (t.gpr .rbp = 0 ↔
      ((word s.mem B (slot w 7)).toNat % 2 ^ b = 0 ∧ (both = true → (word s.mem B (slot w 6)).toNat % 2 ^ b = 0))) := by
    intro t ht
    rw [ht, BitVec.shiftLeft_or_distrib, or_eq_zero, shl_zero_iff _ (by omega_arith)]
    cases both
    · simp
    · simp only [↓reduceIte, shl_zero_iff _ (show b ≤ 64 by omega_arith), forall_const]
  have shv : (1 ≤ 64 - b ∧ 64 - b ≤ 63) = True := eq_true ⟨by omega_arith, by omega_arith⟩
  have hmid : WP isa (.block (([.mov .rax (.mem (at0 .rbx))] : List Instr) ++
      (if both = true then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      ([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr))) s₂ fun t =>
      (t.gpr .rbp = (word s.mem B (slot w 7) ||| (if both then word s.mem B (slot w 6) else 0)) <<< (64 - b) ∧
        t.mem = s₂.mem) ∧ Keep [.rax, .rbp] s₂ t := by
    cases both
    · exact WP.keep [.rax, .rbp] (by
        simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append]
        xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs.ld (d := slot w 7) (by omega_arith), m₂, m₁, shv]
        rw [show (Bignum.word s.mem B (slot w 7) ||| 0) = Bignum.word s.mem B (slot w 7) from BitVec.or_zero]) rfl
    · exact WP.keep [.rax, .rbp] (by
        simp only [↓reduceIte, List.cons_append, List.nil_append]
        xrun [State.ea, at0, hbx, h10, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
          hs.ld (d := slot w 7) (by omega_arith), hs.ld (d := slot w 6) (by omega_arith), m₂, m₁, shv]) rfl
  refine WP.mono hmid fun s₃ ⟨⟨hbp, m₃⟩, k₃⟩ => ?_
  have h₃ : Ws s₃ B Z w := h.congrP (P := fun _ => False) (fun _ _ => by rw [m₃, m₂, m₁]) (fun _ f => f.elim)
    ((k₁.trans k₂).trans k₃) (by simp)
  refine WP.mono (keepOf_ok h₃ (hz s₃ hbp)) fun t ⟨m₄, k₄⟩ => ?_
  exact ⟨by rw [m₄, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans k₄).mono (by simp)⟩

/-! ## Shifts by whole words -/

theorem ofNat_sub64 {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- A number's words from `c` on: it shifted right by `64 c` bits. -/
theorem wv_div_pow (m : Mem) (B : Addr) (d : Nat) {n c : Nat} (hc : c ≤ n) :
    wv m B d n / 2 ^ (64 * c) = wv m B (d + 8 * c) (n - c) := by
  have e := wv_add m B d c (n - c)
  rw [show c + (n - c) = n by omega_arith] at e
  rw [e, Nat.mul_comm (2 ^ (64 * c)), Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (wv_lt _ _ _ _), Nat.zero_add]

/-- A number shifted left by `64 c` bits, modulo `2^(64 n)`: its low `n - c`
words at word `c`. -/
theorem wv_mul_pow_mod (m : Mem) (B : Addr) (d : Nat) {n c : Nat} (hc : c ≤ n) :
    wv m B d n * 2 ^ (64 * c) % 2 ^ (64 * n) = 2 ^ (64 * c) * wv m B d (n - c) := by
  have e := wv_add m B d (n - c) c
  rw [show n - c + c = n by omega_arith] at e
  have hp : 2 ^ (64 * n) = 2 ^ (64 * c) * 2 ^ (64 * (n - c)) := by rw [← Nat.pow_add]; congr 1; omega_arith
  rw [e, hp, Nat.mul_comm _ (2 ^ (64 * c)), Nat.mul_mod_mul_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (wv_lt _ _ _ _)]

/-- `shrWords`' block: `w - c` words from word `c` of `[j]` to `[t]`. -/
theorem shrWB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j c t : Nat} (hc : c ≤ 64) (hcw : c ≤ w) :
    WP isa (.block (ws ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
      ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx)) s fun u =>
      u.gpr .r12 = BitVec.ofNat 64 (w - c) ∧ u.gpr .rsi = off B (slot w j + 8 * c) ∧
        u.gpr .rbx = off B (slot w t) ∧ u.mem = s.mem ∧ Keep [.r12, .r9, .rsi, .rbx] s u := by
  have hw2 := h.w2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = BitVec.ofNat 64 w - BitVec.ofNat 64 c ∧ u.mem = s₁.mem)
    (by xrun [h12, sx_ofNat (show c < 2 ^ 31 by omega_arith)]) rfl) fun s₂ ⟨⟨h12', m₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok j (r := .rsi) (by decide) (((k₁.trans k₂).gpr (by decide)).trans h.rdi)
    ((k₂.gpr (by decide)).trans h9)) fun s₃ ⟨hsi, m₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun u => u.gpr .rsi = off B (slot w j + 8 * c) ∧ u.mem = s₃.mem)
    (by xrun [hsi, sx_ofNat (show 8 * c < 2 ^ 31 by omega_arith), off_addN]) rfl) fun s₄ ⟨⟨hsi', m₄⟩, k₄⟩ => ?_
  refine WP.mono (base_ok t (r := .rbx) (by decide) ((((k₁.trans k₂).trans k₃).trans k₄ |>.gpr (by decide)).trans h.rdi)
    (((k₂.trans k₃).trans k₄ |>.gpr (by decide)).trans h9)) fun u ⟨hbx, m₅, k₅⟩ => ?_
  refine ⟨?_, (k₅.gpr (by decide)).trans hsi', hbx, by rw [m₅, m₄, m₃, m₂, m₁],
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by simp)⟩
  rw [((k₃.trans k₄).trans k₅ |>.gpr (by decide)), h12', ofNat_sub64 (by omega_arith) (by omega_arith)]

/-- `shrWords j c t`: `[t] := [j] / 2^(64 c)`, over `[t]`'s `w + 2` words. -/
theorem shrWords_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j c t : Nat}
    (hj : j < 16) (ht : t < 16) (hjt : j ≠ t) (hc : 1 ≤ c) (hcw : c + 1 ≤ w) (hc64 : c ≤ 64) :
    WP isa (seqs (shrWords j c t)) s fun u =>
      wv u.mem B (slot w t) (w + 2) = wv s.mem B (slot w j) w / 2 ^ (64 * c) ∧
      Outside B (slot w t) (8 * (w + 2)) s.mem u.mem ∧ Keep [.r12, .r9, .r8, .rax, .r14, .rsi, .rbx] s u := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have st := h.sl ht
  have pj := slot_far (w := w) hjt
  have hw2 := h.w2
  simp only [shrWords, seqs]
  refine WP.seq (WP.mono (zeroA_ok h ht) fun s₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  refine WP.seq (WP.mono (shrWB_ok h₁ hc64 (by omega_arith)) fun s₂ ⟨h12, hsi, hbx, m₂, k₂⟩ => ?_)
  have hs₂ := h₁.scr.congr k₂.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hs₂.ld (by omega_arith)) (fun i hi => hs₂.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun u ⟨v, _, o, k₃⟩ => ?_
  rw [m₂] at v o
  have hi : wv u.mem B (slot w t + 8 * (w - c)) (c + 2) = 0 := by
    rw [o.wv (by omega_arith) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
      rw [show slot w t + 8 * (w - c) + 8 * q = slot w t + 8 * (w - c + q) by omega_arith]
      exact (wv_eq_zero_iff _ _ _ _).mp z1 _ (by omega_arith)
  refine ⟨?_, ?_, ((k1.trans k₂).trans k₃).mono (by simp)⟩
  · have sp := wv_add u.mem B (slot w t) (w - c) (c + 2)
    rw [show w - c + (c + 2) = w + 2 by omega_arith, hi, Nat.mul_zero, Nat.add_zero] at sp
    rw [sp, v, o1.wv (by omega_arith) (by omega_arith), wv_div_pow _ _ _ (by omega_arith), Nat.add_zero]
  · intro x hx
    rw [← o1 x hx]
    exact o x (by omega_arith)

theorem slot_add (w j k : Nat) : slot w (j + k) = slot w j + k * (8 * (w + 2)) := by
  simp only [Bignum.slot, Nat.add_mul, Nat.add_assoc]

theorem slot_mono {w j k : Nat} (h : j ≤ k) : slot w j ≤ slot w k :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- `shlWords true`' block: `2 w + 2 - c` words of `[j]` to word `c` of `[t]`. -/
theorem shlWB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j c t : Nat} (hc : c ≤ 64)
    (hcw : c ≤ w) :
    WP isa (.block (wsW true ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
      base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))) s fun u =>
      u.gpr .r12 = BitVec.ofNat 64 (2 * w + 2 - c) ∧ u.gpr .rsi = off B (slot w j) ∧
        u.gpr .rbx = off B (slot w t + 8 * c) ∧ u.mem = s.mem ∧ Keep [.r12, .r9, .rsi, .rbx] s u := by
  have hw2 := h.w2
  unfold wsW
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wideIf_ok true h12) fun s₂ ⟨⟨h12₂, m₂⟩, k₂⟩ => ?_
  simp only [shlN, ↓reduceIte] at h12₂
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = BitVec.ofNat 64 (2 * w + 2) - BitVec.ofNat 64 c ∧
    u.mem = s₂.mem) (by xrun [h12₂, sx_ofNat (show c < 2 ^ 31 by omega_arith)]) rfl) fun s₃ ⟨⟨h12', m₃⟩, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (base2_ok j t (r₁ := .rsi) (r₂ := .rbx) (w := w) (by decide) (by decide) (by decide)
    ((k13.gpr (by decide)).trans h.rdi) (((k₂.trans k₃).gpr (by decide)).trans h9) (by decide))
    fun s₄ ⟨hsi, hbx, m₄, k₄⟩ => ?_
  refine WP.mono (WP.keep [.rbx] (Q := fun u => u.gpr .rbx = off B (slot w t + 8 * c) ∧ u.mem = s₄.mem)
    (by xrun [hbx, sx_ofNat (show 8 * c < 2 ^ 31 by omega_arith), off_addN]) rfl) fun u ⟨⟨hbx', m₅⟩, k₅⟩ => ?_
  refine ⟨?_, (k₅.gpr (by decide)).trans hsi, hbx', by rw [m₅, m₄, m₃, m₂, m₁],
    ((k13.trans k₄).trans k₅).mono (by simp)⟩
  rw [((k₄.trans k₅).gpr (by decide)), h12', ofNat_sub64 (by omega_arith) (by omega_arith)]

/-- `shlWords true j c t`: `[t] := [j] 2^(64 c)` modulo `2^(64 (2 w + 2))`, over
the two arrays from `t` (`j` and `t` two arrays each). -/
theorem shlWords_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j c t : Nat}
    (hj : j + 2 ≤ 16) (ht : t + 2 ≤ 16) (hjt : j + 2 ≤ t ∨ t + 2 ≤ j) (hc : 1 ≤ c) (hcw : c + 2 ≤ w)
    (hc64 : c ≤ 64) :
    WP isa (seqs (shlWords true j c t)) s fun u =>
      wv u.mem B (slot w t) (2 * w + 2) = wv s.mem B (slot w j) (2 * w + 2) * 2 ^ (64 * c) % 2 ^ (64 * (2 * w + 2)) ∧
      Outside B (slot w t) (16 * (w + 2)) s.mem u.mem ∧ Keep [.r12, .r9, .r8, .rax, .r14, .rsi, .rbx] s u := by
  have hn := h.scr.nowrap
  have st := h.sl (j := t + 1) (by omega_arith)
  have sj := h.sl (j := j + 1) (by omega_arith)
  have hw2 := h.w2
  have e1 : slot w (t + 1) = slot w t + 8 * (w + 2) := by rw [slot_add]; omega_arith
  have e2 : slot w (j + 1) = slot w j + 8 * (w + 2) := by rw [slot_add]; omega_arith
  have pj : slot w j + 16 * (w + 2) ≤ slot w t ∨ slot w t + 16 * (w + 2) ≤ slot w j := by
    rcases hjt with h' | h'
    · left; have := slot_mono (w := w) h'; rw [slot_add] at this; omega_arith
    · right; have := slot_mono (w := w) h'; rw [slot_add] at this; omega_arith
  simp only [shlWords, ↓reduceIte, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (zeroA_ok h (j := t) (by omega_arith)) fun s₁ ⟨z1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  refine WP.seq (WP.mono (zeroA_ok h₁ (j := t + 1) (by omega_arith)) fun s₂ ⟨_, o2, k2⟩ => ?_)
  have h₂ := h₁.congrO o2 (slot_256 _ _) k2 (by simp)
  refine WP.seq (WP.mono (shlWB_ok h₂ hc64 (by omega_arith)) fun s₃ ⟨h12, hsi, hbx, m₃, k₃⟩ => ?_)
  have hs₃ := h₂.scr.congr k₃.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => hs₃.ld (by omega_arith)) (fun i hi => hs₃.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun u ⟨v, _, o, k₄⟩ => ?_
  rw [m₃] at v o
  have lo : wv u.mem B (slot w t) c = 0 := by
    rw [o.wv (by omega_arith) (by omega_arith), o2.wv (by omega_arith) (by omega_arith)]
    exact (wv_eq_zero_iff _ _ _ _).mpr fun q hq => (wv_eq_zero_iff _ _ _ _).mp z1 q (by omega_arith)
  have Jv : wv s₂.mem B (slot w j) (2 * w + 2 - c) = wv s.mem B (slot w j) (2 * w + 2 - c) := by
    rw [o2.wv (by omega_arith) (by omega_arith), o1.wv (by omega_arith) (by omega_arith)]
  refine ⟨?_, ?_, ((((k1.trans k2).trans k₃).trans k₄).mono (by simp))⟩
  · have sp := wv_add u.mem B (slot w t) c (2 * w + 2 - c)
    rw [show c + (2 * w + 2 - c) = 2 * w + 2 by omega_arith, lo, Nat.zero_add] at sp
    rw [sp, v, Jv, wv_mul_pow_mod _ _ _ (by omega_arith)]
  · intro x hx
    rw [← o1 x (by omega_arith), ← o2 x (by rw [e1] at *; omega_arith)]
    exact o x (by omega_arith)

/-! ## Shifts by bits -/

/-- A block that leaves the count `c` in `rcx` and changes nothing else. -/
def ClPre (B : Addr) (Z : Nat) (m : Mem) (pre : List Instr) (c : Nat) : Prop :=
  ∀ t : State, Scr t B Z → t.gpr .rdi = B → (∀ i < 32, word t.mem B (8 * i) = word m B (8 * i)) →
    WP isa (.block pre) t fun t' => (t'.gpr .rcx = BitVec.ofNat 64 c ∧ t'.mem = t.mem) ∧ Keep [.rcx] t t'

theorem clOf_pre {B : Addr} {Z : Nat} {m : Mem} {b : Nat} (hb : b < 2 ^ 32) : ClPre B Z m (clOf b) b :=
  fun _ _ _ _ => WP.keep [.rcx] (by unfold clOf; xrun [setW32 hb]) rfl

theorem sC_pre {B : Addr} {Z : Nat} {m : Mem} {c : Nat} (hZ : 8 * 32 ≤ Z)
    (hm : word m B (8 * sC) = BitVec.ofNat 64 c) : ClPre B Z m [.mov .rcx (.mem (hdr sC))] c := fun t ht hdi hh =>
  WP.keep [.rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 c ∧ t'.mem = t.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, ht.ld (d := 8 * sC) (by unfold sC sFn; omega_arith),
      hh sC (by unfold sC sFn; omega_arith), hm]) rfl

/-- The block of a shift by bits: the bases, the width and the count. -/
theorem clBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (wd : Bool) {j t c : Nat} {pre : List Instr}
    (hpre : ClPre B Z s.mem pre c) :
    WP isa (.block (wsW wd ++ base j .r8 ++ base t .rsi ++ pre)) s fun u =>
      u.gpr .r12 = BitVec.ofNat 64 (shlN wd w) ∧ u.gpr .r8 = off B (slot w j) ∧ u.gpr .rsi = off B (slot w t) ∧
        u.gpr .rcx = BitVec.ofNat 64 c ∧ u.mem = s.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rcx] s u := by
  unfold wsW
  rw [show ws ++ (if wd then wideR else []) ++ base j .r8 ++ base t .rsi ++ pre =
    ws ++ ((if wd then wideR else []) ++ ((base j .r8 ++ base t .rsi) ++ pre)) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wideIf_ok wd h12) fun s₂ ⟨⟨h12₂, m₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base2_ok j t (r₁ := .r8) (r₂ := .rsi) (w := w) (by decide) (by decide)
    (by decide) (((k₁.trans k₂).gpr (by decide)).trans h.rdi) ((k₂.gpr (by decide)).trans h9) (by decide))
    fun s₃ ⟨h8, hsi, m₃, k₃⟩ => ?_
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (hpre s₃ (h.scr.congr k13.2.2) ((k13.gpr (by decide)).trans h.rdi)
    (fun i _ => by rw [m₃, m₂, m₁])) fun u ⟨⟨hcx, m₄⟩, k₄⟩ => ?_
  exact ⟨(k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h12₂), (k₄.gpr (by decide)).trans h8,
    (k₄.gpr (by decide)).trans hsi, hcx, by rw [m₄, m₃, m₂, m₁], (k13.trans k₄).mono (by simp)⟩

/-- `x 2^c + r = y` for `r < 2^c`: `x = ⌊y / 2^c⌋`. -/
theorem eq_div_of {x r y c : Nat} (h : x * 2 ^ c + r = y) (hr : r < 2 ^ c) : x = y / 2 ^ c := by
  rw [← h, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hr, Nat.zero_add]

/-- `shrCl false j t pre`: `[t] := [j] / 2^c` over `w` words, for `[j]`'s word `w` zero. -/
theorem shrClP_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j t c : Nat} {pre : List Instr}
    (hj : j < 16) (ht : t < 16) (hjt : j ≠ t) (hc : c < 64) (hpre : ClPre B Z s.mem pre c)
    (hz : word s.mem B (slot w j + 8 * w) = 0) :
    WP isa (shrCl false j t pre) s fun u =>
      wv u.mem B (slot w t) w = wv s.mem B (slot w j) w / 2 ^ c ∧
      Outside B (slot w t) (8 * w) s.mem u.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rcx, .rax, .rdx, .r14] s u := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have st := h.sl ht
  have pj := slot_far (w := w) hjt
  have hw1 := h.w1
  have hw2 := h.w2
  unfold shrCl
  refine WP.seq (WP.mono (clBlk_ok h false hpre) fun s₁ ⟨h12, h8, hsi, hcx, m₁, k₁⟩ => ?_)
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at h12
  refine WP.mono (shrCl_ok hc (h.scr.congr k₁.2.2) hsi h8 h12 hcx (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨v, o, k₂⟩ => ?_
  rw [m₁, hz] at v
  rw [m₁] at o
  refine ⟨eq_div_of (r := (word s.mem B (slot w j)).toNat % 2 ^ c) ?_ (Nat.mod_lt _ (Nat.two_pow_pos _)), o,
    (k₁.trans k₂).mono (by simp)⟩
  rw [v]; simp

/-- `shlCl wd j t pre`: `[t] := [j] 2^c` modulo `2^(64 N)`, `N` words (`2 w + 2` if `wd`). -/
theorem shlClP_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (wd : Bool) {j t c : Nat} {pre : List Instr}
    (hj : j + (if wd then 2 else 1) ≤ 16) (ht : t + (if wd then 2 else 1) ≤ 16)
    (hjt : slot w j + 8 * shlN wd w ≤ slot w t ∨ slot w t + 8 * shlN wd w ≤ slot w j)
    (hc : c < 64) (hpre : ClPre B Z s.mem pre c) :
    WP isa (shlCl wd j t pre) s fun u =>
      wv u.mem B (slot w t) (shlN wd w) = wv s.mem B (slot w j) (shlN wd w) * 2 ^ c % 2 ^ (64 * shlN wd w) ∧
      Outside B (slot w t) (8 * shlN wd w) s.mem u.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rcx, .rax, .rdx, .r14] s u := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sj : slot w j + 8 * shlN wd w ≤ Z := by
    have := slot_room (w := w) hj
    cases wd <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at this hj ⊢ <;> omega_arith
  have st : slot w t + 8 * shlN wd w ≤ Z := by
    have := slot_room (w := w) ht
    cases wd <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at this ht ⊢ <;> omega_arith
  have hN2 : 2 ≤ shlN wd w := by cases wd <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] <;> omega_arith
  have hN3 : shlN wd w < 2 ^ 31 := by cases wd <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] <;> omega_arith
  unfold shlCl
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (clBlk_ok h wd hpre) fun s₁ ⟨h12, h8, hsi, hcx, m₁, k₁⟩ =>
    WP.mono (WP.keep [.rax] (Q := fun u => u.mem = s₁.mem.writeW (off B (slot w t))
      (word s.mem B (slot w j) <<< c)) (by
    xrun [State.ea, at0, h8, hsi, hcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      (h.scr.congr k₁.2.2).ld (d := slot w j) (by omega_arith), (h.scr.congr k₁.2.2).st (d := slot w t) (by omega_arith),
      m₁, execShiftCl, VarShiftOp.eval, cl_eq hc]) rfl)
    fun s₂ ⟨m₂, k₂⟩ => (show WP isa (wordLoop 1 shlClBody) s₂ _ from ?_)))
  have hs₁ := h.scr.congr k₁.2.2
  have hs₂ := hs₁.congr k₂.2.2
  refine WP.mono (shlCl_ok hc hs₂ ((k₂.gpr (by decide)).trans hsi) ((k₂.gpr (by decide)).trans h8)
    ((k₂.gpr (by decide)).trans h12) ((k₂.gpr (by decide)).trans hcx) hN2 hN3 st sj hjt.symm (by
      rw [m₂, word_writeW_self, (writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith), m₁,
        BitVec.toNat_shiftLeft, Nat.shiftLeft_eq])) fun u ⟨v, w0, o, k₃⟩ => ?_
  have Jv : wv s₂.mem B (slot w j) (shlN wd w) = wv s.mem B (slot w j) (shlN wd w) := by
    rw [m₂, (writeW_outside _ _ _ (by omega_arith)).wv (by omega_arith) (by omega_arith), m₁]
  refine ⟨by rw [v, Jv], ?_, ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  intro x hx
  rw [o x (by omega_arith), m₂, writeW_outside _ _ _ (by omega_arith) x (by omega_arith), m₁]

/-! ## A number's shift, selected -/

/-- Two writes, each outside the other's... frame: a frame of two ranges. -/
theorem frm2 {B : Addr} {o₁ n₁ o₂ n₂ : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Outside B o₁ n₁ m₁ m₂)
    (h₂ : Outside B o₂ n₂ m₂ m₃) : Frm B [(o₁, n₁), (o₂, n₂)] m₁ m₃ :=
  (Frm.of_outside h₁ (by simp)).trans (Frm.of_outside h₂ (by simp))

/-- `[j] := keep ? [j] : [j] / 2^(64 c)` over `w` words, through `[14]`. -/
theorem selShrW_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j c : Nat} (hj : j < 14)
    (hc : 1 ≤ c) (hcw : c + 2 ≤ w) (hc64 : c ≤ 64) {keep : Bool}
    (hk : word s.mem B (8 * sB2) = mask keep) :
    WP isa (seqs (shrWords j c 14 ++ [selK false j 14])) s fun t =>
      wv t.mem B (slot w j) w =
        (if keep then wv s.mem B (slot w j) w else wv s.mem B (slot w j) w / 2 ^ (64 * c)) ∧
      Frm B [(slot w 14, 8 * (w + 2)), (slot w j, 8 * w)] s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := h.scr.nowrap
  have sj := h.sl (j := j) (by omega_arith)
  have s14 := h.sl (j := 14) (by decide)
  have pj := slot_far (w := w) (show j ≠ 14 by omega_arith)
  refine wp_seqs_append (by simp [shrWords]) (by simp) (WP.mono (shrWords_ok h (by omega_arith) (by decide)
    (by omega_arith) hc (by omega_arith) hc64) fun s₁ ⟨v1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  simp only [seqs]
  refine WP.mono (selK_ok h₁ false (j := j) (t := 14) (keep := keep) (by simp; omega_arith) (by simp) (by
    simp only [shlN, Bool.false_eq_true, ↓reduceIte]; omega_arith)
    (by rw [o1.word (by unfold sB2 sFn; have := slot_256 w 14; omega_arith)
      (by unfold sB2 sFn; have := h.h256; omega_arith)]; exact hk))
    fun t ⟨v2, o2, k2⟩ => ?_
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v2 o2
  have Jv : wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := o1.wv (by omega_arith) (by omega_arith)
  have Tv : wv s₁.mem B (slot w 14) w = wv s.mem B (slot w j) w / 2 ^ (64 * c) := by
    rw [Key.wv_low (k := w) (n := w + 2) (by omega_arith) (by
      rw [v1]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (wv_lt _ _ _ _)), v1]
  refine ⟨by rw [v2, Jv, Tv], frm2 o1 o2, (k1.trans k2).mono (by simp [mmRegs]),
    h₁.congrO o2 (slot_256 _ _) k2 (by simp)⟩

/-- `x := keep ? x : x 2^(64 c)` modulo `2^(64 (2 w + 2))` (`x` wide array 4), through `[14]`. -/
theorem selShlW_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat}
    (hc : 1 ≤ c) (hcw : c + 2 ≤ w) (hc64 : c ≤ 64) {keep : Bool}
    (hk : word s.mem B (8 * sB2) = mask keep) :
    WP isa (seqs (shlWords true 4 c 14 ++ [selK true 4 14])) s fun t =>
      wv t.mem B (slot w 4) (2 * w + 2) = (if keep then wv s.mem B (slot w 4) (2 * w + 2) else
        wv s.mem B (slot w 4) (2 * w + 2) * 2 ^ (64 * c) % 2 ^ (64 * (2 * w + 2))) ∧
      Frm B [(slot w 14, 16 * (w + 2)), (slot w 4, 8 * (2 * w + 2))] s.mem t.mem ∧ Keep mmRegs s t ∧
        Ws t B Z w := by
  have hn := h.scr.nowrap
  have s15 := h.sl (j := 15) (by decide)
  have e14 : slot w 15 = slot w 14 + 1 * (8 * (w + 2)) := slot_add w 14 1
  have e4 : slot w 14 = slot w 4 + 10 * (8 * (w + 2)) := slot_add w 4 10
  refine wp_seqs_append (by simp [shlWords]) (by simp) (WP.mono (shlWords_ok h (j := 4) (t := 14) (by decide)
    (by decide) (by decide) hc hcw hc64) fun s₁ ⟨v1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  simp only [seqs]
  refine WP.mono (selK_ok h₁ true (j := 4) (t := 14) (keep := keep) (by simp) (by simp) (by
    simp only [shlN, ↓reduceIte]; omega_arith)
    (by rw [o1.word (by unfold sB2 sFn; have := slot_256 w 14; omega_arith)
      (by unfold sB2 sFn; have := h.h256; omega_arith)]; exact hk))
    fun t ⟨v2, o2, k2⟩ => ?_
  simp only [shlN, ↓reduceIte] at v2 o2
  have Jv : wv s₁.mem B (slot w 4) (2 * w + 2) = wv s.mem B (slot w 4) (2 * w + 2) :=
    o1.wv (by omega_arith) (by omega_arith)
  refine ⟨by rw [v2, Jv, v1], frm2 o1 o2, (k1.trans k2).mono (by simp [mmRegs]),
    h₁.congrO o2 (slot_256 _ _) k2 (by simp)⟩

/-- `[j] := keep ? [j] : [j] / 2^b` over `w` words, through `[14]`, for `[j]`'s word `w` zero. -/
theorem selShrB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j b : Nat} (hj : j < 14)
    (hb : b < 64) (hz : word s.mem B (slot w j + 8 * w) = 0) {keep : Bool}
    (hk : word s.mem B (8 * sB2) = mask keep) :
    WP isa (seqs [shrCl false j 14 (clOf b), selK false j 14]) s fun t =>
      wv t.mem B (slot w j) w =
        (if keep then wv s.mem B (slot w j) w else wv s.mem B (slot w j) w / 2 ^ b) ∧
      Frm B [(slot w 14, 8 * w), (slot w j, 8 * w)] s.mem t.mem ∧ Keep mmRegs s t ∧ Ws t B Z w := by
  have hn := h.scr.nowrap
  have sj := h.sl (j := j) (by omega_arith)
  have s14 := h.sl (j := 14) (by decide)
  have pj := slot_far (w := w) (show j ≠ 14 by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (shrClP_ok h (j := j) (t := 14) (by omega_arith) (by decide) (by omega_arith) hb
    (clOf_pre (by omega_arith)) hz) fun s₁ ⟨v1, o1, k1⟩ => ?_)
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  refine WP.mono (selK_ok h₁ false (j := j) (t := 14) (keep := keep) (by simp; omega_arith) (by simp) (by
    simp only [shlN, Bool.false_eq_true, ↓reduceIte]; omega_arith)
    (by rw [o1.word (by unfold sB2 sFn; have := slot_256 w 14; omega_arith)
      (by unfold sB2 sFn; have := h.h256; omega_arith)]; exact hk))
    fun t ⟨v2, o2, k2⟩ => ?_
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at v2 o2
  have Jv : wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := o1.wv (by omega_arith) (by omega_arith)
  refine ⟨by rw [v2, Jv, v1], frm2 o1 o2, (k1.trans k2).mono (by simp [mmRegs]),
    h₁.congrO o2 (slot_256 _ _) k2 (by simp)⟩

/-- `x := keep ? x : x 2^b` modulo `2^(64 (2 w + 2))` (`x` wide array 4), through `[14]`. -/
theorem selShlB_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {b : Nat}
    (hb : b < 64) {keep : Bool} (hk : word s.mem B (8 * sB2) = mask keep) :
    WP isa (seqs [shlCl true 4 14 (clOf b), selK true 4 14]) s fun t =>
      wv t.mem B (slot w 4) (2 * w + 2) = (if keep then wv s.mem B (slot w 4) (2 * w + 2) else
        wv s.mem B (slot w 4) (2 * w + 2) * 2 ^ b % 2 ^ (64 * (2 * w + 2))) ∧
      Frm B [(slot w 14, 8 * (2 * w + 2)), (slot w 4, 8 * (2 * w + 2))] s.mem t.mem ∧ Keep mmRegs s t ∧
        Ws t B Z w := by
  have hn := h.scr.nowrap
  have s15 := h.sl (j := 15) (by decide)
  have e14 : slot w 15 = slot w 14 + 1 * (8 * (w + 2)) := slot_add w 14 1
  have e4 : slot w 14 = slot w 4 + 10 * (8 * (w + 2)) := slot_add w 4 10
  simp only [seqs]
  refine WP.seq (WP.mono (shlClP_ok h true (j := 4) (t := 14) (by simp) (by simp) (by
    simp only [shlN, ↓reduceIte]; omega_arith) hb (clOf_pre (by omega_arith))) fun s₁ ⟨v1, o1, k1⟩ => ?_)
  simp only [shlN, ↓reduceIte] at v1 o1
  have h₁ := h.congrO o1 (slot_256 _ _) k1 (by simp)
  refine WP.mono (selK_ok h₁ true (j := 4) (t := 14) (keep := keep) (by simp) (by simp) (by
    simp only [shlN, ↓reduceIte]; omega_arith)
    (by rw [o1.word (by unfold sB2 sFn; have := slot_256 w 14; omega_arith)
      (by unfold sB2 sFn; have := h.h256; omega_arith)]; exact hk))
    fun t ⟨v2, o2, k2⟩ => ?_
  simp only [shlN, ↓reduceIte] at v2 o2
  have Jv : wv s₁.mem B (slot w 4) (2 * w + 2) = wv s.mem B (slot w 4) (2 * w + 2) :=
    o1.wv (by omega_arith) (by omega_arith)
  refine ⟨by rw [v2, Jv, v1], frm2 o1 o2, (k1.trans k2).mono (by simp [mmRegs]),
    h₁.congrO o2 (slot_256 _ _) k2 (by simp)⟩

/-! ## A stage -/

theorem slotE (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := rfl

/-- The twos' numbers: `u` (array 7) and `x₂` (array 6) of `w` words, each
with word `w` zero, and `x` (wide array 4) of `2 w + 2`. -/
structure TwV (t : State) (B : Addr) (Z w u x2 x : Nat) : Prop where
  ws : Ws t B Z w
  u : wv t.mem B (slot w 7) w = u
  uz : word t.mem B (slot w 7 + 8 * w) = 0
  x2 : wv t.mem B (slot w 6) w = x2
  x2z : word t.mem B (slot w 6 + 8 * w) = 0
  x : wv t.mem B (slot w 4) (2 * w + 2) = x

/-- What the stages change: arrays 4 to 7, the temporary's two and `sB2`. -/
def twRs (w : Nat) : List (Nat × Nat) :=
  [(slot w 4, 32 * (w + 2)), (slot w 14, 16 * (w + 2)), (8 * sB2, 8)]

/-- A stage's test: the low `s` bits of `u` zero, and of `x₂` if `both`. -/
def StZ (u x2 s : Nat) (both : Bool) : Prop := u % 2 ^ s = 0 ∧ (both = true → x2 % 2 ^ s = 0)

instance (u x2 s : Nat) (both : Bool) : Decidable (StZ u x2 s both) := by unfold StZ; infer_instance

theorem wv_mod_low (m : Mem) (B : Addr) (d : Nat) {c n : Nat} (hc : c ≤ n) :
    wv m B d n % 2 ^ (64 * c) = wv m B d c := by
  have e := wv_add m B d c (n - c)
  rw [show c + (n - c) = n by omega_arith] at e
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wv_lt _ _ _ _)]

theorem if_not_decide {α : Type} (z : Prop) [Decidable z] (a b : α) :
    (if (!decide z) = true then a else b) = if z then b else a := by
  by_cases hz : z <;> simp [hz]

/-- A frame within the stages' ranges. -/
theorem tw_cover {B : Addr} {w : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (f : Frm B rs m m')
    (hc : ∀ r ∈ rs, ∃ r' ∈ twRs w, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Frm B (twRs w) m m' :=
  WordDivide.cover f hc

macro "tw_sep" : tactic =>
  `(tactic| (
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨by omega_arith, by omega_arith⟩))

/-- A stage of `c` words, taken (`c + 2 ≤ w`): where the test holds, `u` (and
`x₂` if `both`) shift right and `x` (if `both`) left by `64 c` bits. -/
theorem stageWT_ok {s : State} {B : Addr} {Z w u x2 x : Nat} (hV : TwV s B Z w u x2 x) (both : Bool) {c : Nat}
    (hc : 1 ≤ c) (hcw : c + 2 ≤ w) (hc64 : c ≤ 64) :
    WP isa (seqs (testW both c ++ shrWords 7 c 14 ++ [selK false 7 14] ++
      (if both then shrWords 6 c 14 ++ [selK false 6 14] ++ shlWords true 4 c 14 ++ [selK true 4 14] else []))) s
      fun t => TwV t B Z w (if StZ u x2 (64 * c) both then u / 2 ^ (64 * c) else u)
        (if both ∧ StZ u x2 (64 * c) both then x2 / 2 ^ (64 * c) else x2)
        (if both ∧ StZ u x2 (64 * c) both then x * 2 ^ (64 * c) % 2 ^ (64 * (2 * w + 2)) else x) ∧
        Frm B (twRs w) s.mem t.mem ∧ Keep mmRegs s t := by
  have h := hV.ws
  have hn := h.scr.nowrap
  have hZ := h.hZ
  rw [slotE] at hZ
  have hw2 := h.w2
  have sl4 := slotE w 4
  have sl6 := slotE w 6
  have sl7 := slotE w 7
  have sl14 := slotE w 14
  have hsb : 8 * sB2 = 216 := rfl
  have hz : (wv s.mem B (slot w 7) c = 0 ∧ (both = true → wv s.mem B (slot w 6) c = 0)) ↔
      StZ u x2 (64 * c) both := by
    unfold StZ
    rw [← hV.u, ← hV.x2, wv_mod_low _ _ _ (show c ≤ w by omega_arith), wv_mod_low _ _ _ (show c ≤ w by omega_arith)]
  have hst : 8 * sB2 + 8 ≤ 256 := by unfold sB2 sFn; omega_arith
  refine wp_seqs_append (a := testW both c) (by simp [testW]) (by cases both <;> simp [shrWords])
    (WP.mono (testW_ok h both hc (by omega_arith)) fun s₁ ⟨m₁, k₁⟩ => ?_)
  rw [decide_eq_decide.mpr hz] at m₁
  have h₁ := h.congrW m₁ (by unfold DOk; simp only [sB2, sFn]; omega_arith) (by decide) k₁ (by simp)
  have o₁ : Outside B (8 * sB2) 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_arith)
  have hk₁ : word s₁.mem B (8 * sB2) = mask (!decide (StZ u x2 (64 * c) both)) := by rw [m₁, word_writeW_self]
  have fo₁ : Frm B (twRs w) s.mem s₁.mem := Frm.of_outside o₁ (by simp [twRs])
  have e7 : wv s₁.mem B (slot w 7) w = u := by rw [o₁.wv (by omega_arith) (by omega_arith), hV.u]
  have e6 : wv s₁.mem B (slot w 6) w = x2 := by rw [o₁.wv (by omega_arith) (by omega_arith), hV.x2]
  have e4 : wv s₁.mem B (slot w 4) (2 * w + 2) = x := by
    rw [o₁.wv (by omega_arith) (by omega_arith), hV.x]
  have z7 : word s₁.mem B (slot w 7 + 8 * w) = 0 := by rw [o₁.word (by omega_arith) (by omega_arith), hV.uz]
  have z6 : word s₁.mem B (slot w 6 + 8 * w) = 0 := by rw [o₁.word (by omega_arith) (by omega_arith), hV.x2z]
  cases both
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (selShrW_ok h₁ (j := 7) (by decide) hc hcw hc64 hk₁) fun t ⟨v, f, k, ht⟩ => ?_
    rw [if_not_decide, e7] at v
    refine ⟨⟨ht, v, ?_, ?_, ?_, ?_⟩, fo₁.trans (tw_cover f ?_), (k₁.trans k).mono (by simp [mmRegs])⟩
    · rw [f.word_eq (by tw_sep) (by omega_arith), z7]
    · rw [f.wv_eq (by tw_sep) (by omega_arith), e6]; simp only [false_and, ↓reduceIte]
    · rw [f.word_eq (by tw_sep) (by omega_arith), z6]
    · rw [f.wv_eq (by tw_sep) (by omega_arith), e4]; simp only [false_and, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
        ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩
  · simp only [↓reduceIte, true_and]
    show WP isa (seqs ((shrWords 7 c 14 ++ [selK false 7 14]) ++
      ((shrWords 6 c 14 ++ [selK false 6 14]) ++ (shlWords true 4 c 14 ++ [selK true 4 14])))) s₁ _
    refine wp_seqs_append (by simp [shrWords]) (by simp [shrWords])
      (WP.mono (selShrW_ok h₁ (j := 7) (by decide) hc hcw hc64 hk₁) fun s₂ ⟨v7, f7, k7, h₂⟩ => ?_)
    rw [if_not_decide, e7] at v7
    have hk₂ : word s₂.mem B (8 * sB2) = mask (!decide (StZ u x2 (64 * c) true)) := by
      rw [f7.word_eq (by tw_sep) (by omega_arith), hk₁]
    refine wp_seqs_append (by simp [shrWords]) (by simp [shlWords])
      (WP.mono (selShrW_ok h₂ (j := 6) (by decide) hc hcw hc64 hk₂) fun s₃ ⟨v6, f6, k6, h₃⟩ => ?_)
    rw [if_not_decide, f7.wv_eq (by tw_sep) (by omega_arith), e6] at v6
    have hk₃ : word s₃.mem B (8 * sB2) = mask (!decide (StZ u x2 (64 * c) true)) := by
      rw [f6.word_eq (by tw_sep) (by omega_arith), hk₂]
    refine WP.mono (selShlW_ok h₃ hc hcw hc64 hk₃) fun t ⟨v4, f4, k4, ht⟩ => ?_
    rw [if_not_decide, f6.wv_eq (by tw_sep) (by omega_arith), f7.wv_eq (by tw_sep) (by omega_arith), e4] at v4
    refine ⟨⟨ht, ?_, ?_, ?_, ?_, v4⟩, ?_, (((k₁.trans k7).trans k6).trans k4).mono (by simp [mmRegs])⟩
    · rw [f4.wv_eq (by tw_sep) (by omega_arith), f6.wv_eq (by tw_sep) (by omega_arith), v7]
    · rw [f4.word_eq (by tw_sep) (by omega_arith), f6.word_eq (by tw_sep) (by omega_arith),
        f7.word_eq (by tw_sep) (by omega_arith), z7]
    · rw [f4.wv_eq (by tw_sep) (by omega_arith), v6]
    · rw [f4.word_eq (by tw_sep) (by omega_arith), f6.word_eq (by tw_sep) (by omega_arith),
        f7.word_eq (by tw_sep) (by omega_arith), z6]
    · refine fo₁.trans (((tw_cover f7 ?_).trans (tw_cover f6 ?_)).trans (tw_cover f4 ?_)) <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      · exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩
      · exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩
      · exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩

/-- A stage's guard: `CF` of `w < c + 2`. -/
theorem stageHd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat} (hc : c ≤ 64) :
    WP isa (.block (ws ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 2)))] : List Instr))) s fun t =>
      (t.cf = some (decide (w < c + 2)) ∧ t.mem = s.mem) ∧ Keep [.r12, .r9] s t := by
  have hw2 := h.w2
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.cf = some (decide (w < c + 2)) ∧ t.mem = s₁.mem) (by
    xrun [h12, sx_ofNat (show c + 2 < 2 ^ 31 by omega_arith)]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show c + 2 < 2 ^ 64 by omega_arith)]) rfl) fun t ⟨⟨hcf, m₂⟩, k₂⟩ => ⟨⟨hcf, by rw [m₂, m₁]⟩, (k₁.trans k₂).mono (by simp)⟩

theorem TwV.congrM {s t : State} {B : Addr} {Z w u x2 x : Nat} (hV : TwV s B Z w u x2 x) (hm : t.mem = s.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : TwV t B Z w u x2 x :=
  ⟨hV.ws.congrP (P := fun _ => False) (fun _ _ => by rw [hm]) (fun _ f => f.elim) k hr,
    by rw [hm]; exact hV.u, by rw [hm]; exact hV.uz, by rw [hm]; exact hV.x2, by rw [hm]; exact hV.x2z,
    by rw [hm]; exact hV.x⟩

/-- A stage of `c` words, taken where `c + 2 ≤ w` and its test holds. -/
theorem stageW_ok {s : State} {B : Addr} {Z w u x2 x : Nat} (hV : TwV s B Z w u x2 x) (both : Bool) {c : Nat}
    (hc : 1 ≤ c) (hc64 : c ≤ 64) :
    WP isa (stageW both c) s fun t =>
      TwV t B Z w (if c + 2 ≤ w ∧ StZ u x2 (64 * c) both then u / 2 ^ (64 * c) else u)
        (if both ∧ (c + 2 ≤ w ∧ StZ u x2 (64 * c) both) then x2 / 2 ^ (64 * c) else x2)
        (if both ∧ (c + 2 ≤ w ∧ StZ u x2 (64 * c) both) then x * 2 ^ (64 * c) % 2 ^ (64 * (2 * w + 2)) else x) ∧
        Frm B (twRs w) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold stageW
  refine WP.seq (WP.mono (stageHd_ok hV.ws hc64) fun s₁ ⟨⟨hcf, m₁⟩, k₁⟩ => ?_)
  have hV₁ := hV.congrM m₁ k₁ (by simp)
  refine WP.ite (decide (w < c + 2)) (by simp only [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · have hg : ¬ (c + 2 ≤ w) := by simp only [decide_eq_true_eq] at hb; omega_arith
    refine WP.block_nil_iff.mpr ⟨?_, ?_, k₁.mono (by simp [mmRegs])⟩
    · simp only [hg, false_and, and_false, ↓reduceIte]; exact hV₁
    · rw [m₁]; exact Frm.refl _ _ _
  · have hg : c + 2 ≤ w := by simp only [decide_eq_false_iff_not] at hb; omega_arith
    refine WP.mono (stageWT_ok hV₁ both hc hg hc64) fun t ⟨tv, f, k⟩ => ⟨?_, by rw [← m₁]; exact f,
      (k₁.trans k).mono (by simp [mmRegs])⟩
    simp only [hg, true_and]; exact tv

/-- A number's low `b ≤ 64` bits are its low word's. -/
theorem wv_mod_word (m : Mem) (B : Addr) (d : Nat) {n b : Nat} (hn : 1 ≤ n) (hb : b ≤ 64) :
    wv m B d n % 2 ^ b = (word m B d).toNat % 2 ^ b := by
  have e := wv_add m B d 1 (n - 1)
  rw [show 1 + (n - 1) = n by omega_arith] at e
  have e1 : wv m B d 1 = (word m B d).toNat := by
    simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add]
  have hp : 2 ^ (64 * 1) = 2 ^ b * 2 ^ (64 - b) := by rw [← Nat.pow_add]; congr 1; omega_arith
  rw [e, e1, hp, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- A stage of `b` bits: where its test holds, `u` (and `x₂` if `both`) shift
right and `x` (if `both`) left by `b` bits. -/
theorem stageB_ok {s : State} {B : Addr} {Z w u x2 x : Nat} (hV : TwV s B Z w u x2 x) (both : Bool) {b : Nat}
    (hb : 1 ≤ b) (hb32 : b ≤ 32) :
    WP isa (seqs (stageB both b)) s
      fun t => TwV t B Z w (if StZ u x2 b both then u / 2 ^ b else u)
        (if both ∧ StZ u x2 b both then x2 / 2 ^ b else x2)
        (if both ∧ StZ u x2 b both then x * 2 ^ b % 2 ^ (64 * (2 * w + 2)) else x) ∧
        Frm B (twRs w) s.mem t.mem ∧ Keep mmRegs s t := by
  have h := hV.ws
  have hn := h.scr.nowrap
  have hZ := h.hZ
  rw [slotE] at hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sl4 := slotE w 4
  have sl6 := slotE w 6
  have sl7 := slotE w 7
  have sl14 := slotE w 14
  have hsb : 8 * sB2 = 216 := rfl
  have hz : ((word s.mem B (slot w 7)).toNat % 2 ^ b = 0 ∧
      (both = true → (word s.mem B (slot w 6)).toNat % 2 ^ b = 0)) ↔ StZ u x2 b both := by
    unfold StZ
    rw [← hV.u, ← hV.x2, wv_mod_word _ _ _ (show 1 ≤ w by omega_arith) (show b ≤ 64 by omega_arith),
      wv_mod_word _ _ _ (show 1 ≤ w by omega_arith) (show b ≤ 64 by omega_arith)]
  unfold stageB
  refine wp_seqs_append (a := testB both b) (by simp [testB]) (by cases both <;> simp)
    (WP.mono (testB_ok h both hb hb32) fun s₁ ⟨m₁, k₁⟩ => ?_)
  rw [decide_eq_decide.mpr hz] at m₁
  have h₁ := h.congrW m₁ (by unfold DOk; simp only [sB2, sFn]; omega_arith) (by decide) k₁ (by simp)
  have o₁ : Outside B (8 * sB2) 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_arith)
  have hk₁ : word s₁.mem B (8 * sB2) = mask (!decide (StZ u x2 b both)) := by rw [m₁, word_writeW_self]
  have fo₁ : Frm B (twRs w) s.mem s₁.mem := Frm.of_outside o₁ (by simp [twRs])
  have e7 : wv s₁.mem B (slot w 7) w = u := by rw [o₁.wv (by omega_arith) (by omega_arith), hV.u]
  have e6 : wv s₁.mem B (slot w 6) w = x2 := by rw [o₁.wv (by omega_arith) (by omega_arith), hV.x2]
  have e4 : wv s₁.mem B (slot w 4) (2 * w + 2) = x := by
    rw [o₁.wv (by omega_arith) (by omega_arith), hV.x]
  have z7 : word s₁.mem B (slot w 7 + 8 * w) = 0 := by rw [o₁.word (by omega_arith) (by omega_arith), hV.uz]
  have z6 : word s₁.mem B (slot w 6 + 8 * w) = 0 := by rw [o₁.word (by omega_arith) (by omega_arith), hV.x2z]
  cases both
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (selShrB_ok h₁ (j := 7) (by decide) (by omega_arith) z7 hk₁) fun t ⟨v, f, k, ht⟩ => ?_
    rw [if_not_decide, e7] at v
    refine ⟨⟨ht, v, ?_, ?_, ?_, ?_⟩, fo₁.trans (tw_cover f ?_), (k₁.trans k).mono (by simp [mmRegs])⟩
    · rw [f.word_eq (by tw_sep) (by omega_arith), z7]
    · rw [f.wv_eq (by tw_sep) (by omega_arith), e6]; simp only [false_and, ↓reduceIte]
    · rw [f.word_eq (by tw_sep) (by omega_arith), z6]
    · rw [f.wv_eq (by tw_sep) (by omega_arith), e4]; simp only [false_and, ↓reduceIte]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
        ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩
  · simp only [↓reduceIte, true_and]
    show WP isa (seqs ([shrCl false 7 14 (clOf b), selK false 7 14] ++
      ([shrCl false 6 14 (clOf b), selK false 6 14] ++ [shlCl true 4 14 (clOf b), selK true 4 14]))) s₁ _
    refine wp_seqs_append (by simp) (by simp)
      (WP.mono (selShrB_ok h₁ (j := 7) (by decide) (by omega_arith) z7 hk₁) fun s₂ ⟨v7, f7, k7, h₂⟩ => ?_)
    rw [if_not_decide, e7] at v7
    have hk₂ : word s₂.mem B (8 * sB2) = mask (!decide (StZ u x2 b true)) := by
      rw [f7.word_eq (by tw_sep) (by omega_arith), hk₁]
    have z6₂ : word s₂.mem B (slot w 6 + 8 * w) = 0 := by rw [f7.word_eq (by tw_sep) (by omega_arith), z6]
    refine wp_seqs_append (by simp) (by simp)
      (WP.mono (selShrB_ok h₂ (j := 6) (by decide) (by omega_arith) z6₂ hk₂) fun s₃ ⟨v6, f6, k6, h₃⟩ => ?_)
    rw [if_not_decide, f7.wv_eq (by tw_sep) (by omega_arith), e6] at v6
    have hk₃ : word s₃.mem B (8 * sB2) = mask (!decide (StZ u x2 b true)) := by
      rw [f6.word_eq (by tw_sep) (by omega_arith), hk₂]
    refine WP.mono (selShlB_ok h₃ (by omega_arith) hk₃) fun t ⟨v4, f4, k4, ht⟩ => ?_
    rw [if_not_decide, f6.wv_eq (by tw_sep) (by omega_arith), f7.wv_eq (by tw_sep) (by omega_arith), e4] at v4
    refine ⟨⟨ht, ?_, ?_, ?_, ?_, v4⟩, ?_, (((k₁.trans k7).trans k6).trans k4).mono (by simp [mmRegs])⟩
    · rw [f4.wv_eq (by tw_sep) (by omega_arith), f6.wv_eq (by tw_sep) (by omega_arith), v7]
    · rw [f4.word_eq (by tw_sep) (by omega_arith), f6.word_eq (by tw_sep) (by omega_arith),
        f7.word_eq (by tw_sep) (by omega_arith), z7]
    · rw [f4.wv_eq (by tw_sep) (by omega_arith), v6]
    · rw [f4.word_eq (by tw_sep) (by omega_arith), f6.word_eq (by tw_sep) (by omega_arith), z6₂]
    · refine fo₁.trans (((tw_cover f7 ?_).trans (tw_cover f6 ?_)).trans (tw_cover f4 ?_)) <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      · exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩
      · exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩
      · exact ⟨⟨(slot w 14, 16 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩,
          ⟨(slot w 4, 32 * (w + 2)), by simp [twRs], by omega_arith, by omega_arith⟩⟩

/-! ## The stages in turn -/

open VG.Proof.Bignum.ShiftStages in
/-- Stages `f c` in turn, each taking its size `g c` where it fits below `T`:
together they take `greedy T (cs.map g) a`. -/
theorem wp_stages {Inv : Nat → State → Prop} {R : State → State → Prop}
    (hR : ∀ {a b c : State}, R a b → R b c → R a c) {f : Nat → List (Prog isa)} (hf : ∀ c, f c ≠ [])
    {g : Nat → Nat} {T : Nat} {cs : List Nat}
    (hs : ∀ c ∈ cs, ∀ a s, Inv a s → WP isa (seqs (f c)) s fun t =>
      Inv (if a + g c ≤ T then a + g c else a) t ∧ R s t) :
    ∀ (a : Nat) (s : State), cs ≠ [] → Inv a s →
      WP isa (seqs ((cs.map f).flatten)) s fun t => Inv (greedy T (cs.map g) a) t ∧ R s t := by
  induction cs with
  | nil => intro _ _ h; exact absurd rfl h
  | cons c cs ih =>
    intro a s _ hI
    cases cs with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
        greedy_cons, greedy_nil]
      exact hs c (by simp) a s hI
    | cons c' cs' =>
      simp only [List.map_cons, List.flatten_cons, greedy_cons]
      refine wp_seqs_append (hf c) (by simp [hf c']) (WP.mono (hs c (by simp) a s hI) fun t ⟨h1, r1⟩ => ?_)
      refine WP.mono (ih (fun c hc => hs c (List.mem_cons_of_mem _ hc)) _ t (by simp) h1) fun t' ⟨h2, r2⟩ => ?_
      simp only [List.map_cons] at h2
      exact ⟨h2, hR r1 r2⟩

open VG.Proof.Bignum.ShiftStages

theorem greedy_append (T : Nat) (l₁ l₂ : List Nat) (a : Nat) :
    greedy T (l₁ ++ l₂) a = greedy T l₂ (greedy T l₁ a) := by
  simp only [greedy, List.foldl_append]

theorem stages_pows : (wordStages.map (64 * ·)) ++ bitStages.map id = pows 12 := by decide

theorem twR_trans {B : Addr} {w : Nat} {a b c : State} (h₁ : Frm B (twRs w) a.mem b.mem ∧ Keep mmRegs a b)
    (h₂ : Frm B (twRs w) b.mem c.mem ∧ Keep mmRegs b c) : Frm B (twRs w) a.mem c.mem ∧ Keep mmRegs a c :=
  ⟨h₁.1.trans h₂.1, (h₁.2.trans h₂.2).mono (by simp [mmRegs])⟩

/-- The twos common to `u` and `x₂`, `T = tz (gcd u x₂)`, off both and onto `x`. -/
theorem twosBoth_ok {s : State} {B : Addr} {Z w U X2 X : Nat} (hV : TwV s B Z w U X2 X) (hU0 : U ≠ 0)
    (hUw : U < 2 ^ (64 * (w - 1))) (hw : w ≤ 129) (hX : X < 2 ^ (64 * (2 * w + 2))) :
    WP isa (seqs (wordStages.map (stageW true) ++ (bitStages.map (stageB true)).flatten)) s fun t =>
      TwV t B Z w (U / 2 ^ tz (Nat.gcd U X2)) (X2 / 2 ^ tz (Nat.gcd U X2))
        (X * 2 ^ tz (Nat.gcd U X2) % 2 ^ (64 * (2 * w + 2))) ∧
      Frm B (twRs w) s.mem t.mem ∧ Keep mmRegs s t := by
  generalize hT : tz (Nat.gcd U X2) = T
  have hg0 : Nat.gcd U X2 ≠ 0 := Nat.gcd_ne_zero_left hU0
  have hTU : T ≤ tz U := hT ▸ (dvd_iff hU0 _).mp
    (Nat.dvd_trans ((dvd_iff hg0 _).mpr (Nat.le_refl _)) (Nat.gcd_dvd_left U X2))
  have hTw : tz U < 64 * (w - 1) := tz_lt (Nat.pos_of_ne_zero hU0) hUw
  let Inv : Nat → State → Prop := fun a t =>
    a ≤ T ∧ TwV t B Z w (U / 2 ^ a) (X2 / 2 ^ a) (X * 2 ^ a % 2 ^ (64 * (2 * w + 2)))
  have hstep : ∀ {a sz : Nat} {G : Prop} [Decidable G], a ≤ T → (G ↔ a + sz ≤ T) → ∀ {t : State},
      TwV t B Z w (if G then U / 2 ^ a / 2 ^ sz else U / 2 ^ a)
        (if true = true ∧ G then X2 / 2 ^ a / 2 ^ sz else X2 / 2 ^ a)
        (if true = true ∧ G then X * 2 ^ a % 2 ^ (64 * (2 * w + 2)) * 2 ^ sz % 2 ^ (64 * (2 * w + 2))
          else X * 2 ^ a % 2 ^ (64 * (2 * w + 2))) →
      Inv (if a + sz ≤ T then a + sz else a) t := by
    intro a sz G _ ha hG t tv
    by_cases hl : a + sz ≤ T
    · simp only [hG.mpr hl, true_and, ↓reduceIte, div_pow_add, mul_pow_add_mod] at tv
      simp only [hl, ↓reduceIte]; exact ⟨hl, tv⟩
    · have : ¬ G := fun g => hl (hG.mp g)
      simp only [this, true_and, ↓reduceIte] at tv
      simp only [hl, ↓reduceIte]; exact ⟨ha, tv⟩
  have hW := wp_stages (Inv := Inv) (R := fun a b => Frm B (twRs w) a.mem b.mem ∧ Keep mmRegs a b) twR_trans
    (f := fun c => [stageW true c]) (fun _ => by simp) (g := (64 * ·)) (T := T) (cs := wordStages)
    (fun c hc a t ⟨ha, tv⟩ => by
      have hc' : 1 ≤ c ∧ c ≤ 64 := by simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc; omega_arith
      refine WP.mono (stageW_ok tv true hc'.1 hc'.2) fun t' ⟨tv', f, k⟩ => ⟨hstep ha ?_ tv', f, k⟩
      simp only [StZ, forall_const]
      rw [stage_pair hU0 (hT ▸ ha)]
      constructor
      · exact fun h => hT ▸ h.2
      · intro h; exact ⟨by omega_arith, hT ▸ h⟩)
  have hB := wp_stages (Inv := Inv) (R := fun a b => Frm B (twRs w) a.mem b.mem ∧ Keep mmRegs a b) twR_trans
    (f := stageB true) (fun _ => by simp [stageB, testB]) (g := id) (T := T) (cs := bitStages)
    (fun b hb a t ⟨ha, tv⟩ => by
      have hb' : 1 ≤ b ∧ b ≤ 32 := by simp only [bitStages, List.mem_cons, List.not_mem_nil, or_false] at hb; omega_arith
      refine WP.mono (stageB_ok tv true hb'.1 hb'.2) fun t' ⟨tv', f, k⟩ => ⟨hstep ha ?_ tv', f, k⟩
      simp only [StZ, forall_const]
      rw [stage_pair hU0 (hT ▸ ha)]
      exact ⟨fun h => hT ▸ h, fun h => hT ▸ h⟩)
  have h0 : Inv 0 s := ⟨Nat.zero_le _, by simpa [Nat.mod_eq_of_lt hX] using hV⟩
  refine wp_seqs_append (by simp [wordStages]) (by simp [bitStages, stageB, testB])
    (WP.mono (show WP isa (seqs ((wordStages.map fun c => [stageW true c]).flatten)) s _ from
      hW 0 s (by simp [wordStages]) h0) fun t₁ ⟨hI₁, r₁⟩ => ?_)
  refine WP.mono (hB _ t₁ (by simp [bitStages]) hI₁) fun t ⟨⟨_, tv⟩, r₂⟩ => ?_
  have e : greedy T (bitStages.map id) (greedy T (wordStages.map (64 * ·)) 0) = T := by
    rw [← greedy_append, stages_pows]
    exact greedy_pows 12 T 0 (Nat.zero_le _) (by omega_arith)
  rw [e] at tv
  exact ⟨tv, twR_trans r₁ r₂⟩

/-- `u`'s own twos, from `b₀ ≤ tz u` of them taken: `x₂` and `x` unchanged. -/
theorem twosU_ok {s : State} {B : Addr} {Z w U X2 X b₀ : Nat} (hV : TwV s B Z w (U / 2 ^ b₀) X2 X) (hU0 : U ≠ 0)
    (hUw : U < 2 ^ (64 * (w - 1))) (hw : w ≤ 129) (hb₀ : b₀ ≤ tz U) :
    WP isa (seqs (wordStages.map (stageW false) ++ (bitStages.map (stageB false)).flatten)) s fun t =>
      TwV t B Z w (U / 2 ^ tz U) X2 X ∧ Frm B (twRs w) s.mem t.mem ∧ Keep mmRegs s t := by
  generalize hT : tz U = T at hb₀
  have hTw : T < 64 * (w - 1) := hT ▸ tz_lt (Nat.pos_of_ne_zero hU0) hUw
  let Inv : Nat → State → Prop := fun a t => b₀ ≤ a ∧ a ≤ T ∧ TwV t B Z w (U / 2 ^ a) X2 X
  have hstep : ∀ {a sz : Nat} {G : Prop} [Decidable G], b₀ ≤ a → a ≤ T → (G ↔ a + sz ≤ T) → ∀ {t : State},
      TwV t B Z w (if G then U / 2 ^ a / 2 ^ sz else U / 2 ^ a)
        (if false = true ∧ G then X2 / 2 ^ sz else X2)
        (if false = true ∧ G then X * 2 ^ sz % 2 ^ (64 * (2 * w + 2)) else X) →
      Inv (if a + sz ≤ T then a + sz else a) t := by
    intro a sz G _ ha ha' hG t tv
    simp only [Bool.false_eq_true, false_and, ↓reduceIte] at tv
    by_cases hl : a + sz ≤ T
    · simp only [hG.mpr hl, ↓reduceIte, div_pow_add] at tv
      simp only [hl, ↓reduceIte]; exact ⟨by omega_arith, hl, tv⟩
    · have : ¬ G := fun g => hl (hG.mp g)
      simp only [this, ↓reduceIte] at tv
      simp only [hl, ↓reduceIte]; exact ⟨ha, ha', tv⟩
  have hW := wp_stages (Inv := Inv) (R := fun a b => Frm B (twRs w) a.mem b.mem ∧ Keep mmRegs a b) twR_trans
    (f := fun c => [stageW false c]) (fun _ => by simp) (g := (64 * ·)) (T := T) (cs := wordStages)
    (fun c hc a t ⟨ha, ha', tv⟩ => by
      have hc' : 1 ≤ c ∧ c ≤ 64 := by simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc; omega_arith
      refine WP.mono (stageW_ok tv false hc'.1 hc'.2) fun t' ⟨tv', f, k⟩ => ⟨hstep ha ha' ?_ tv', f, k⟩
      simp only [StZ, Bool.false_eq_true, false_implies, and_true]
      rw [stage_tz hU0 (hT ▸ ha'), hT]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨by omega_arith, h⟩)
  have hB := wp_stages (Inv := Inv) (R := fun a b => Frm B (twRs w) a.mem b.mem ∧ Keep mmRegs a b) twR_trans
    (f := stageB false) (fun _ => by simp [stageB, testB]) (g := id) (T := T) (cs := bitStages)
    (fun b hb a t ⟨ha, ha', tv⟩ => by
      have hb' : 1 ≤ b ∧ b ≤ 32 := by simp only [bitStages, List.mem_cons, List.not_mem_nil, or_false] at hb; omega_arith
      refine WP.mono (stageB_ok tv false hb'.1 hb'.2) fun t' ⟨tv', f, k⟩ => ⟨hstep ha ha' ?_ tv', f, k⟩
      simp only [StZ, Bool.false_eq_true, false_implies, and_true]
      rw [stage_tz hU0 (hT ▸ ha'), hT]; rfl)
  refine wp_seqs_append (by simp [wordStages]) (by simp [bitStages, stageB, testB])
    (WP.mono (show WP isa (seqs ((wordStages.map fun c => [stageW false c]).flatten)) s _ from
      hW b₀ s (by simp [wordStages]) ⟨Nat.le_refl _, hb₀, hV⟩) fun t₁ ⟨hI₁, r₁⟩ => ?_)
  refine WP.mono (hB _ t₁ (by simp [bitStages]) hI₁) fun t ⟨⟨_, _, tv⟩, r₂⟩ => ?_
  have e : greedy T (bitStages.map id) (greedy T (wordStages.map (64 * ·)) b₀) = T := by
    rw [← greedy_append, stages_pows]
    exact greedy_pows 12 T b₀ hb₀ (by omega_arith)
  rw [e] at tv
  exact ⟨tv, twR_trans r₁ r₂⟩

/-- `twos`: `u := u / 2^(tz u)`, `x₂ := x₂ / 2^T`, `x := x 2^T mod 2^(64 (2 w + 2))`
for `T = tz (gcd u x₂)`. -/
theorem twos_ok {s : State} {B : Addr} {Z w U X2 X : Nat} (hV : TwV s B Z w U X2 X) (hU0 : U ≠ 0)
    (hUw : U < 2 ^ (64 * (w - 1))) (hw : w ≤ 129) (hX : X < 2 ^ (64 * (2 * w + 2))) :
    WP isa (seqs twos) s fun t =>
      TwV t B Z w (U / 2 ^ tz U) (X2 / 2 ^ tz (Nat.gcd U X2))
        (X * 2 ^ tz (Nat.gcd U X2) % 2 ^ (64 * (2 * w + 2))) ∧
      Frm B (twRs w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg0 : Nat.gcd U X2 ≠ 0 := Nat.gcd_ne_zero_left hU0
  have hTU : tz (Nat.gcd U X2) ≤ tz U := (dvd_iff hU0 _).mp
    (Nat.dvd_trans ((dvd_iff hg0 _).mpr (Nat.le_refl _)) (Nat.gcd_dvd_left U X2))
  unfold twos
  rw [show wordStages.map (stageW true) ++ (bitStages.map (stageB true)).flatten ++ wordStages.map (stageW false) ++
      (bitStages.map (stageB false)).flatten = (wordStages.map (stageW true) ++ (bitStages.map (stageB true)).flatten) ++
      (wordStages.map (stageW false) ++ (bitStages.map (stageB false)).flatten) by simp only [List.append_assoc]]
  refine wp_seqs_append (by simp [wordStages]) (by simp [wordStages])
    (WP.mono (twosBoth_ok hV hU0 hUw hw hX) fun t₁ ⟨tv₁, r₁⟩ => ?_)
  exact WP.mono (twosU_ok tv₁ hU0 hUw hw hTU) fun t ⟨tv, r₂⟩ => ⟨tv, twR_trans r₁ r₂⟩

/-! ## Leading zeros -/

/-- A stage of `b` bits of `rdx`'s leading zeros, counted in `r11`. -/
theorem clzStage_ok {s : State} {b : Nat} (hb : 1 ≤ b) (hb' : b ≤ 32) {v : BitVec 64} {a : Nat}
    (hdx : s.gpr .rdx = v) (h11 : s.gpr .r11 = BitVec.ofNat 64 a) :
    WP isa (.block (clzStage b)) s fun t =>
      (t.gpr .rdx = (if v >>> (64 - b) = 0 then v <<< b else v) ∧
        t.gpr .r11 = BitVec.ofNat 64 (if v >>> (64 - b) = 0 then a + b else a) ∧ t.mem = s.mem) ∧
      Keep [.rcx, .r8, .rdx, .r9, .r11] s t := by
  refine WP.keep [.rcx, .r8, .rdx, .r9, .r11] ?_ rfl
  have shv : (1 ≤ 64 - b ∧ 64 - b ≤ 63) = True := eq_true ⟨by omega_arith, by omega_arith⟩
  have shb : (1 ≤ b ∧ b ≤ 63) = True := eq_true ⟨by omega_arith, by omega_arith⟩
  unfold clzStage
  by_cases hz : v >>> (64 - b) = 0
  · xrun [hdx, h11, shv, shb, sx_ofNat (show b < 2 ^ 31 by omega_arith), execCmov, eval, readSrc,
      show BitVec.toNat (1 : BitVec 64) = (1 : BitVec 64).toNat from rfl, decide_lt_one', hz]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide True))) = BitVec.allOnes 64 from rfl,
      BitVec.allOnes_and, BitVec.ofNat_add]
  · xrun [hdx, h11, shv, shb, sx_ofNat (show b < 2 ^ 31 by omega_arith), execCmov, eval, readSrc,
      show BitVec.toNat (1 : BitVec 64) = (1 : BitVec 64).toNat from rfl, decide_lt_one', hz]
    rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide False))) = 0#64 from rfl, BitVec.zero_and,
      BitVec.add_zero]

/-- The stages of leading zeros in turn: `(rdx, count)`. -/
def clzF (v : BitVec 64) (a : Nat) : List Nat → BitVec 64 × Nat
  | [] => (v, a)
  | b :: bs => if v >>> (64 - b) = 0 then clzF (v <<< b) (a + b) bs else clzF v a bs

theorem clzStages_ok : ∀ (bs : List Nat), (∀ b ∈ bs, 1 ≤ b ∧ b ≤ 32) → ∀ {s : State} {v : BitVec 64} {a : Nat},
    s.gpr .rdx = v → s.gpr .r11 = BitVec.ofNat 64 a →
    WP isa (.block (bs.map clzStage).flatten) s fun t =>
      (t.gpr .rdx = (clzF v a bs).1 ∧ t.gpr .r11 = BitVec.ofNat 64 (clzF v a bs).2 ∧ t.mem = s.mem) ∧
      Keep [.rcx, .r8, .rdx, .r9, .r11] s t
  | [], _, s, v, a, hdx, h11 => WP.block_nil_iff.mpr ⟨⟨hdx, h11, rfl⟩, Keep.refl _ _⟩
  | b :: bs, hb, s, v, a, hdx, h11 => by
    simp only [List.map_cons, List.flatten_cons]
    rw [WP.block_append_iff]
    have hb' := hb b (by simp)
    refine WP.mono (clzStage_ok hb'.1 hb'.2 hdx h11) fun t ⟨⟨h1, h2, m⟩, k⟩ => ?_
    refine WP.mono (clzStages_ok bs (fun b' h => hb b' (by simp [h])) h1 h2) fun u ⟨⟨u1, u2, um⟩, k'⟩ => ?_
    refine ⟨⟨?_, ?_, by rw [um, m]⟩, (k.trans k').mono (by simp)⟩ <;>
    · by_cases hz : v >>> (64 - b) = 0
      · simp only [hz, ↓reduceIte] at u1 u2 ⊢; simp only [clzF, hz, ↓reduceIte]; assumption
      · simp only [hz, ↓reduceIte] at u1 u2 ⊢; simp only [clzF, hz, ↓reduceIte]; assumption

theorem ushr_eq_zero_iff (v : BitVec 64) (k : Nat) : v >>> k = 0 ↔ v.toNat < 2 ^ k := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]

/-- The stages of leading zeros of `w ≠ 0` take `greedy` of `63 - log₂ w`. -/
theorem clzF_greedy {w : Nat} (hw0 : w ≠ 0) (hwl : w < 2 ^ 64) : ∀ (bs : List Nat), (∀ b ∈ bs, b ≤ 64) →
    ∀ (v : BitVec 64) (a : Nat), v.toNat = w * 2 ^ a → a ≤ 63 - Nat.log2 w →
    (clzF v a bs).2 = greedy (63 - Nat.log2 w) bs a
  | [], _, v, a, _, _ => rfl
  | b :: bs, hb, v, a, hv, ha => by
    have hb' := hb b (by simp)
    have hlog : Nat.log2 w < 64 := (lt_pow_iff hw0 0 64).mp (by simpa using hwl)
    have key : v >>> (64 - b) = 0 ↔ a + b ≤ 63 - Nat.log2 w := by
      rw [ushr_eq_zero_iff, hv, stage_clz hw0 a b hb']
      exact ⟨fun h => h.1, fun h => ⟨h, hlog⟩⟩
    rw [greedy_cons]
    by_cases hl : a + b ≤ 63 - Nat.log2 w
    · simp only [clzF, key.mpr hl, ↓reduceIte, hl]
      refine clzF_greedy hw0 hwl bs (fun b' h => hb b' (by simp [h])) _ _ ?_ hl
      have hlt : w * 2 ^ (a + b) < 2 ^ 64 := (lt_pow_iff hw0 _ 64).mpr (by omega_arith)
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hv, Nat.mul_assoc, ← Nat.pow_add, Nat.mod_eq_of_lt hlt]
    · simp only [clzF, mt key.mp hl, ↓reduceIte, hl]
      exact clzF_greedy hw0 hwl bs (fun b' h => hb b' (by simp [h])) _ _ hv ha

theorem clzF_zero : ∀ (bs : List Nat), (∀ b ∈ bs, b ≤ 64) → ∀ (a : Nat), (clzF 0 a bs).2 = a + bs.sum
  | [], _, a => by simp [clzF]
  | b :: bs, hb, a => by
    have e1 : (0 : BitVec 64) >>> (64 - b) = 0 := (ushr_eq_zero_iff _ _).mpr (Nat.two_pow_pos _)
    have e2 : (0 : BitVec 64) <<< b = 0 := BitVec.eq_of_toNat_eq (by simp)
    simp only [clzF, e1, ↓reduceIte, e2, List.sum_cons]
    rw [clzF_zero bs (fun b' h => hb b' (by simp [h])) (a + b)]; omega_arith

/-- The count of `w`'s leading zeros: `63 - log₂ w` (`63` for `0`). -/
theorem clzF_val {w : Nat} (hwl : w < 2 ^ 64) :
    (clzF (BitVec.ofNat 64 w) 0 [32, 16, 8, 4, 2, 1]).2 = 63 - Nat.log2 w := by
  by_cases hw0 : w = 0
  · subst hw0; rw [show BitVec.ofNat 64 0 = 0 from rfl, clzF_zero _ (by decide) 0]; rfl
  · rw [clzF_greedy hw0 hwl _ (by decide) _ 0 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwl]; simp)
      (Nat.zero_le _)]
    exact greedy_pows 5 _ 0 (Nat.zero_le _) (by omega_arith)

theorem hOf_ofNat {W : Nat} (hW : 4 ≤ W) (hW' : W < 2 ^ 63) :
    BitVec.ofNat 64 W >>> 1 - 2 = BitVec.ofNat 64 (W / 2 - 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (2 : BitVec 64).toNat = 2 from rfl]
  omega_arith

/-- `clzTop j`: `sC := 63 - log₂` of word `h - 1` of `[j]` (wide, `h = W / 2 - 2`). -/
theorem clzTop_ok {s : State} {B : Addr} {Z W : Nat} (h : Ws s B Z W) {j : Nat} (hj : j < 16) (hW : 6 ≤ W) :
    WP isa (.block (clzTop j)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * sC))
        (BitVec.ofNat 64 (63 - Nat.log2 (word s.mem B (slot W j + 8 * (W / 2 - 2 - 1))).toNat)) ∧
      Keep [.r12, .r9, .rbx, .rcx, .r8, .rdx, .r11] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hw2 := h.w2
  unfold clzTop
  rw [show ws ++ base j .rbx ++ hOf ++ ([.mov .rdx (.mem (ix .rbx .r12 (-8))), .mov32 .r11 (.imm 0)] : List Instr) ++
      ([32, 16, 8, 4, 2, 1].map clzStage).flatten ++ ([.store (hdr sC) .r11] : List Instr) =
    ws ++ (base j .rbx ++ ((hOf ++ ([.mov .rdx (.mem (ix .rbx .r12 (-8))), .mov32 .r11 (.imm 0)] : List Instr)) ++
      (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++ ([.store (hdr sC) .r11] : List Instr)))) by
    simp only [List.append_assoc], WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12, .rdx, .r11] (Q := fun t => t.gpr .rdx = word s.mem B (slot W j + 8 * (W / 2 - 2 - 1)) ∧
      t.gpr .r11 = BitVec.ofNat 64 0 ∧ t.mem = s₂.mem) (by
    simp only [hOf, List.cons_append, List.nil_append]
    xrun [(k₂.gpr (by decide) : s₂.gpr .r12 = _), h12, hOf_ofNat (W := W) (by omega_arith) (by omega_arith),
      State.ea, ix, addrm8 hbx rfl (show 1 ≤ W / 2 - 2 by omega_arith),
      hs₂.ld (d := slot W j + 8 * (W / 2 - 2 - 1)) (by omega_arith), m₂, m₁]
    done) rfl) fun s₃ ⟨⟨hdx, h11, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (clzStages_ok _ (by decide) hdx h11) fun s₄ ⟨⟨_, h11', m₄⟩, k₄⟩ => ?_
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sC))
      (BitVec.ofNat 64 (63 - Nat.log2 (word s.mem B (slot W j + 8 * (W / 2 - 2 - 1))).toNat))) (by
    have hs₄ := h.scr.congr k14.2.2
    have ew : BitVec.ofNat 64 (word s.mem B (slot W j + 8 * (W / 2 - 2 - 1))).toNat =
        word s.mem B (slot W j + 8 * (W / 2 - 2 - 1)) := by simp
    rw [← ew, clzF_val (BitVec.isLt _)] at h11'
    xrun [State.ea, hdr, (k14.gpr (by decide) : s₄.gpr .rdi = _), h.rdi, hdrOff, h11',
      hs₄.st (d := 8 * sC) (by unfold sC sFn; have := h.h256; omega_arith), m₄, m₃, m₂, m₁]) rfl)
    fun t ⟨m₅, k₅⟩ => ⟨m₅, (k14.trans k₅).mono (by simp)⟩

end VG.Proof.Rsa.X86_64.Rd
