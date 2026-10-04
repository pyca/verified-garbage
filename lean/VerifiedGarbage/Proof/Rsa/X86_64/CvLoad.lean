import VerifiedGarbage.Proof.Rsa.X86_64.CvHead

/-!
# `vg_rsa_crt_values` on x86-64: the loads and the check of `p q = n`

`CvS`: what every piece of `main` keeps (the working space, the arguments,
the inputs' bytes, and memory outside the working space), from a frame of
ranges `Mut` allows (`CvS.step`). The loads of `n`, `p`, `q` and `d` and
the mask of `p q = n` (`cvLoad_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The inputs of `vg_rsa_crt_values` and where they are. -/
structure CvIn where
  B : Addr
  Z : Nat
  k : Nat
  pl : Nat
  ql : Nat
  dl : Nat
  pDp : Addr
  pDq : Addr
  pQi : Addr
  pN : Addr
  pP : Addr
  pQ : Addr
  pD : Addr
  sv : Nat → BitVec 64
  nb : List Byte
  pb : List Byte
  qb : List Byte
  db : List Byte

/-- What every piece of `main` keeps, from the memory `m₀` on entry to
`main`. -/
structure CvS (I : CvIn) (m₀ : Mem) (s : State) : Prop where
  ws : Ws s I.B I.Z (wk I.k)
  args : CvArgs s.mem I.B I.k I.pl I.ql I.dl I.pDp I.pDq I.pQi I.pN I.pP I.pQ I.pD I.sv
  n : Src s I.B I.Z I.pN I.nb
  p : Src s I.B I.Z I.pP I.pb
  q : Src s I.B I.Z I.pQ I.qb
  d : Src s I.B I.Z I.pD I.db
  inScr : InScr I.B I.Z m₀ s.mem

theorem CvS.step {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s) {rs : List (Nat × Nat)}
    (hf : Frm I.B rs s.mem t.mem) (hm : ∀ r ∈ rs, Mut r) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ I.Z) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs) : CvS I m₀ t :=
  have hi : InScr I.B I.Z s.mem t.mem := InScr.of_frm hf hz
  ⟨h.ws.congr hf hm k hr, h.args.congr (argSlot_frm hf hm), h.n.congrK hi k, h.p.congrK hi k, h.q.congrK hi k,
    h.d.congrK hi k, h.inScr.trans hi⟩

/-- `CvS` after a piece that changes only array `j`'s first `n` bytes. -/
theorem CvS.arr {I : CvIn} {m₀ : Mem} {s t : State} (h : CvS I m₀ s) {j n : Nat} (hj : j < 16)
    (hn : n ≤ 8 * (wk I.k + 2)) (ho : Outside I.B (slot (wk I.k) j) n s.mem t.mem) {regs : List Reg}
    (k : Keep regs s t) (hr : .rdi ∉ regs) : CvS I m₀ t :=
  h.step (Frm.of_outside ho (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot _ _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; have := h.ws.sl hj; dsimp only; omega) k hr

/-! ## Masks -/

/-- `eqA a b`: `rbp = 0` iff `[a] = [b]` over `w` words. -/
theorem eqA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {a b : Nat} (ha : a < 16) (hb : b < 16) :
    WP isa (seqs (eqA a b)) s fun t =>
      (t.gpr .rbp = 0 ↔ wv s.mem B (slot w a) w = wv s.mem B (slot w b) w) ∧ t.mem = s.mem ∧
        Keep [.r12, .r9, .rbx, .r10, .rbp, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have sa := h.sl ha
  have sb := h.sl hb
  simp only [eqA, seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (Q := fun (t : State) => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w a) ∧ t.gpr .r10 = off B (slot w b) ∧ t.mem = s.mem ∧
      Keep [.r12, .r9, .rbx, .r10] s t) ?_ fun s₁ ⟨h12, hbx, h10, m₁, k₁⟩ =>
    WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = 0 ∧ t.mem = s₁.mem) (by xrun) rfl)
      fun s₂ ⟨⟨hbp, m₂⟩, k₂⟩ => ?_))
  · rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono h.ws_ok fun t₁ ⟨e12, e9, n₁, j₁⟩ => ?_
    refine WP.mono (base2_ok a b (r₁ := .rbx) (r₂ := .r10) (by decide) (by decide) (by decide)
      ((j₁.gpr (by decide)).trans h.rdi) e9 (by decide)) fun t ⟨e1, e2, n₂, j₂⟩ => ?_
    exact ⟨(j₂.gpr (by decide)).trans e12, e1, e2, n₂.trans n₁, (j₁.trans j₂).mono (by simp)⟩
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₂.mem → Keep [.r14] s₂ t → t.cf = s₂.cf →
      OrInv s₂ B Z (fun j => ∀ i < j, word s₂.mem B (slot w a + 8 * i) = word s₂.mem B (slot w b + 8 * i))
        0 t := fun t h14 hm k _ =>
    ⟨hs₂.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₂.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by have := h.w1; omega) (by have := h.w2; omega) _ h0
    (fun j _ hj t hI => xorStep_ok ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h10)
      ((k₂.gpr (by decide)).trans h12) (by have := h.w2; omega) (by omega) (by omega) hj hI)) fun t hI => ?_
  rw [m₂, m₁] at hI
  refine ⟨?_, by rw [hI.mem, m₂, m₁], (k12.trans hI.keep).mono (by simp)⟩
  rw [hI.val]
  exact ⟨fun hw => wv_congr2 fun i hi => hw i hi, fun hw => wv_inj (d := slot w a) (e := slot w b) w hw⟩

theorem decide_lt_one' (x : BitVec 64) : decide (x.toNat < (1 : BitVec 64).toNat) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj,
    show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
  constructor <;> intro h <;> omega

/-- `andZero`: the mask of `rbp = 0` and'ed into `sMask`. -/
theorem andZero_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Bool}
    (hm : word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c) {z : Prop} [Decidable z]
    (hz : s.gpr .rbp = 0 ↔ z) :
    WP isa (.block andZero) s fun t =>
      t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask)) (mask (c && decide z)) ∧ Keep [.rbp] s t := by
  have hl := h.scr.ld (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega)
  have hst := h.scr.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega)
  have e : decide (s.gpr .rbp = 0) = decide z := by
    by_cases hz' : z
    · rw [decide_eq_true hz', decide_eq_true (hz.mpr hz')]
    · rw [decide_eq_false hz', decide_eq_false (fun h => hz' (hz.mp h))]
  refine WP.keep [.rbp] (Q := fun t => t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask))
    (mask (c && decide z))) ?_ rfl
  unfold andZero
  xrun [State.ea, hdr, h.rdi, hdrOff, hl, hst, hm, decide_lt_one', e]
  congr 1
  rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide z))) = mask (decide z) from rfl, BitVec.and_comm,
    mask_and']

/-- `andOdd j`: the mask of `[j]` odd and'ed into `sMask`. -/
theorem andOdd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) {c : Bool}
    (hm : word s.mem B (8 * Impl.Bignum.X86_64.Public.sMask) = mask c) :
    WP isa (.block (andOdd j)) s fun t =>
      t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask))
        (mask (decide (wv s.mem B (slot w j) w % 2 = 1) && c)) ∧
        Keep [.r12, .r9, .rbx, .rax, .rdx] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have hst := h.scr.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega)
  unfold andOdd
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans h.rdi
  have e0 : (s.mem.readW (off B (slot w j)) 64).toNat % 2 = wv s.mem B (slot w j) w % 2 := by
    rw [← wv_mod64 s.mem B (slot w j) (n := w) (by have := h.w1; omega), Nat.mod_mod_of_dvd _ (by decide)]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = s.mem.writeW (off B (8 * Impl.Bignum.X86_64.Public.sMask))
      (mask (decide (wv s.mem B (slot w j) w % 2 = 1) && c))) (by
    xrun [State.ea, at0, hdr, hdi₂, hdrOff, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w j) (by omega), hs₂.ld (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by
        have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega), hs₂.st (d := 8 * Impl.Bignum.X86_64.Public.sMask) (by
        have := h.h256; unfold Impl.Bignum.X86_64.Public.sMask sFn; omega), m₂, m₁, hm, mask_low, e0]
    rw [mask_and']) rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `setOneA j`: word 0 of `[j]` := 1. -/
theorem setOneA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 16) :
    WP isa (.block (setOneA j)) s fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64) ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  unfold setOneA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.st (d := slot w j) (by omega), m₂, m₁]
    rfl) rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

end VG.Proof.Rsa.X86_64
