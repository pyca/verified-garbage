module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Rows
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.SelectX
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # The virtual modulus at a run-time width

`virtualize_ok`: `[2]` replaced by 3 if it is 1 (`InvBatch.virtualize_ok`), its words scanned by a
loop.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Weierstrass.X86.Inv (wordClob)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `seed ||| f 0 ||| … ||| f (n - 1)`. -/
def seededOr (seed : BitVec 32) (f : Nat → BitVec 32) : Nat → BitVec 32
  | 0 => seed
  | n + 1 => seededOr seed f n ||| f n

theorem seededOr_zero (seed : BitVec 32) (f : Nat → BitVec 32) (n : Nat) :
    seededOr seed f n = 0 ↔ seed = 0 ∧ ∀ i < n, f i = 0 := by
  induction n with
  | zero => simp [seededOr]
  | succ n ih =>
    have hor : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
    rw [seededOr, hor, ih]
    constructor
    · rintro ⟨⟨seed, early⟩, last⟩
      refine ⟨seed, fun i hi => ?_⟩
      by_cases lt : i < n
      · exact early i lt
      · have e : i = n := by omega
        simpa only [e] using last
    · rintro ⟨seed, all⟩
      exact ⟨⟨seed, fun i hi => all i (by omega)⟩, all n (by omega)⟩

theorem scan_eq_one (m : Mem) (base : Addr) (M n : Nat) (hn : 0 < n) :
    seededOr (m.readW (off base M) 32 ^^^ 1) (fun j => m.readW (off base (M + 4 * (j + 1))) 32) (n - 1) = 0 ↔
      val32 m base M n = 1 := by
  rw [seededOr_zero]
  have low : (m.readW (off base M) 32 ^^^ 1) = 0 ↔ w32 m base M = 1 := by
    constructor
    · intro h
      have e : m.readW (off base M) 32 = 1 := BitVec.xor_eq_zero_iff.mp h
      rw [w32, e]; rfl
    · intro h
      have e : m.readW (off base M) 32 = 1 := BitVec.eq_of_toNat_eq h
      rw [e]; decide
  rw [low]
  have tail : (∀ i < n - 1, m.readW (off base (M + 4 * (i + 1))) 32 = 0) ↔ val32 m base (M + 4) (n - 1) = 0 := by
    rw [VG.Proof.Weierstrass.val32_eq_zero_iff]
    apply forall_congr'; intro i
    apply forall_congr'; intro _
    rw [show M + 4 * (i + 1) = M + 4 + 4 * i by omega]
    constructor
    · intro h; rw [w32, h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h
  have expanded : val32 m base M n = w32 m base M + 2 ^ 32 * val32 m base (M + 4) (n - 1) :=
    (congrArg (val32 m base M) (show n = (n - 1) + 1 by omega)).trans rfl
  rw [tail, expanded]
  constructor
  · rintro ⟨h, t⟩; omega
  · intro h; omega

theorem virtualize_ok {s : State} (h : Bx L s B Z len N) (hn2 : 2 ≤ nw len) :
    WP isa (virtualize L) s fun t =>
      Bx L t B Z len N ∧
      val32 t.mem B (rv (kw len) (a 2)) (nw len) =
        (if val32 s.mem B (rv (kw len) (a 2)) (nw len) = 1 then 3 else val32 s.mem B (rv (kw len) (a 2)) (nw len)) ∧
      Keeps wordClob s t ∧ Outside B (rv (kw len) (a 2)) 4 s.mem t.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have hf16 := h.fits16
  have hw := kw_bound h.ws.lenLe
  have ke := kw_eq len
  have r2 := rv_a len 2
  let M := rv (kw len) (a 2)
  have hM : M = rv (kw len) (a 2) := rfl
  unfold virtualize
  simp only [List.append_assoc]
  -- The low word less one, a pointer past it and the words left.
  refine WP.seq (ptr_ok h.ws h.slots hZ (r := .ebp) (t := .edx) (x := a 2) (by decide) (by decide)
    (by decide) (by decide) (by intro e; cases e) (by omega) fun u₁ K₁ m₁ p₁ => ?_)
  have hw₁ := h.ws.rt.of_keeps K₁
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_ptr hw₁ p₁ (d := 0) (by omega)) fun u₂ U₂ _ => ?_
  refine wp_logicS (.inr rfl) rfl fun u₃ U₃ => ?_
  refine wp_movS rfl fun u₄ U₄ _ => wp_addS rfl fun u₅ U₅ _ => ?_
  have K₅ : Keeps [.eax, .ebx, .edx, .ebp] s u₅ :=
    ((((K₁.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))).trans
      (U₄.keeps.mono (by decide))).trans (U₅.keeps.mono (by decide))
  have m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, m₁]
  have H₅ : Bx L u₅ B Z len N := h.keep K₅ (by decide) (by decide) (o := 160) (c := 0)
    (by rw [m₅]; exact Outside.refl _ _ _ _) (Nat.le_refl _) (by omega)
  refine nBytesLess_ok H₅.ws.ws.workspace H₅.slots hZ (by omega) (by omega) fun u K₆ m₆ c₆ => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .edx, .ebp, .esi] s u := (K₅.mono (by decide)).trans (K₆.mono (by decide))
  have m : u.mem = s.mem := by rw [m₆, m₅]
  have pe : PtrAt u B .ebp M := by
    rw [PtrAt, K₆.1 _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide),
      U₂.other _ (by decide)]; exact p₁
  have p₄ : PtrAt u₄ B .ebx M := by
    rw [PtrAt, U₄.gpr, U₃.other _ (by decide), U₂.other _ (by decide)]; exact p₁
  have pb : PtrAt u B .ebx (M + 4 + 4 * 0) := by
    rw [PtrAt, K₆.1 _ (by decide), U₅.gpr, ptr_add p₄]
    rfl
  have seed : u.gpr .eax = s.mem.readW (off B M) 32 ^^^ 1 := by
    rw [K₆.1 _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, ite_eq_right (by decide),
      U₂.gpr, m₁, Nat.add_zero]
  have hwu := h.ws.rt.of_keeps K
  -- The scan.
  let f := fun j => s.mem.readW (off B (M + 4 * (j + 1))) 32
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop (N := nw len - 1) (by omega)
    (fun j t => Keeps [.eax, .ebx, .esi] u t ∧ t.mem = u.mem ∧ PtrAt t B .ebx (M + 4 + 4 * j) ∧
      (t.gpr .esi).toNat = 4 * (nw len - 1 - j) ∧ t.gpr .eax = seededOr (s.mem.readW (off B M) 32 ^^^ 1) f j)
    ?_ ⟨Keeps.refl _ _, rfl, pb, by rw [c₆]; omega, seed⟩) fun t ⟨Kt, mt, _, _, Et⟩ => ?_)
  · rintro j t hj ⟨Kt, mt, pt, ct, et⟩
    have hwt := hwu.of_keeps Kt
    refine wp_orS (readSrc_ptr hwt pt (d := 0) (by omega)) fun t₁ T₁ => ?_
    refine wp_addS rfl fun t₂ T₂ _ => VG.Proof.Bignum.X86.CrtRt.wp_subXm rfl fun t₃ T₃ z₃ _ => WP.block_nil ?_
    have esi₃ : (t₃.gpr .esi).toNat = 4 * (nw len - 1 - (j + 1)) := by
      rw [T₃.gpr, T₂.other _ (by decide), T₁.other _ (by decide), BitVec.toNat_sub, ct,
        show (4 : BitVec 32).toNat = 4 from rfl]
      omega
    refine ⟨⟨(Kt.trans ((T₁.keeps.mono (by decide)).trans (T₂.keeps.mono (by decide)))).trans
      (T₃.keeps.mono (by decide)), by rw [T₃.mem, T₂.mem, T₁.mem, mt], ?_, esi₃, ?_⟩, ?_⟩
    · have pt₁ : PtrAt t₁ B .ebx (M + 4 + 4 * j) := by rw [PtrAt, T₁.other _ (by decide)]; exact pt
      rw [PtrAt, T₃.other _ (by decide), T₂.gpr, ptr_add pt₁]
      congr 1
    · rw [T₃.other _ (by decide), T₂.other _ (by decide), T₁.gpr, et, mt, m]
      simp only [seededOr, f, Nat.add_zero]
      rw [show M + 4 + 4 * j = M + 4 * (j + 1) by omega]
    · rw [z₃]
      congr 1
      by_cases e : j + 1 = nw len - 1
      · simp only [e, decide_true, beq_iff_eq]
        exact BitVec.eq_of_toNat_eq (by rw [← T₃.gpr, esi₃, e]; show _ = 0; omega)
      · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro z0
        have := congrArg BitVec.toNat z0
        rw [← T₃.gpr, esi₃, show BitVec.toNat (0 : BitVec 32) = 0 from rfl] at this
        exact e (by omega)
  -- The mask of `2` where all was zero, or'd into the low word.
  have hwt := hwu.of_keeps Kt
  have eq0 : t.gpr .eax = 0 ↔ val32 s.mem B M (nw len) = 1 := by rw [Et]; exact scan_eq_one _ _ _ _ (by omega)
  refine wp_subS rfl fun t₄ T₄ cf₄ => ?_
  refine wp_sbbS rfl cf₄ fun t₅ T₅ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t₆ T₆ => ?_
  have mask : t₆.gpr .eax = if val32 s.mem B M (nw len) = 1 then 2 else 0 := by
    rw [T₆.gpr, ite_eq_left rfl, T₅.gpr, BitVec.sub_self]
    by_cases hz : t.gpr .eax = 0
    · rw [hz]; have e := eq0.mp hz; rw [ite_eq_left e]; rfl
    · have nz : ¬(t.gpr .eax).toNat < 1 := by
        intro lt; have z : (t.gpr .eax).toNat = 0 := by omega
        exact hz (BitVec.eq_of_toNat_eq z)
      have hne : ¬(t.gpr .eax).toNat < BitVec.toNat (1 : BitVec 32) := nz
      rw [decide_eq_false hne]
      rw [ite_eq_right (fun e => hz (eq0.mpr e))]; rfl
  have K₆' : Keeps [.eax] t t₆ := (T₄.keeps.trans T₅.keeps).trans T₆.keeps
  have pe₆ : PtrAt t₆ B .ebp M := by rw [PtrAt, K₆'.1 _ (by decide), Kt.1 _ (by decide)]; exact pe
  have hw₆ := hwt.of_keeps K₆'
  have mem₆ : t₆.mem = s.mem := by rw [T₆.mem, T₅.mem, T₄.mem, mt, m]
  refine wp_movS (readSrc_ptr hw₆ pe₆ (d := 0) (by omega)) fun t₇ T₇ _ => ?_
  refine wp_orS rfl fun t₈ T₈ => ?_
  have K₈ : Keeps [.eax, .ecx] t t₈ := ((K₆'.mono (by decide)).trans (T₇.keeps.mono (by decide))).trans
    (T₈.keeps.mono (by decide))
  have hw₈ := hwt.of_keeps K₈
  have pe₈ : PtrAt t₈ B .ebp M := by rw [PtrAt, K₈.1 _ (by decide), Kt.1 _ (by decide)]; exact pe
  have ea : t₈.ea (at_ .ebp 0) = off B M := by simpa using ea_ptr hw₈ pe₈ (d := 0) (by omega)
  refine wp_storeS ea (ws_write hw₈ (by omega)) fun v V => WP.block_nil ?_
  have mem₈ : t₈.mem = s.mem := by rw [T₈.mem, T₇.mem, mem₆]
  have frame : Outside B M 4 s.mem v.mem := by
    rw [V.mem, mem₈]; exact writeW32_outside _ _ _ (by omega)
  have KK : Keeps wordClob s v :=
    (((K.mono (by decide)).trans (Kt.mono (by decide))).trans (K₈.mono (by decide))).trans (V.keeps _)
  refine ⟨h.keep KK (by decide) (by decide) frame (by omega) (by omega), ?_, KK, frame⟩
  have stored : w32 v.mem B M = (t₈.gpr .ecx).toNat := by rw [V.mem, w32_write_self]
  have expanded (mm : Mem) : val32 mm B M (nw len) = w32 mm B M + 2 ^ 32 * val32 mm B (M + 4) (nw len - 1) :=
    (congrArg (val32 mm B M) (show nw len = (nw len - 1) + 1 by omega)).trans rfl
  rw [expanded, stored, frame.val32 (by omega) (by omega)]
  rw [T₈.gpr, T₇.gpr, T₇.other .eax (by decide), mask, mem₆, Nat.add_zero]
  by_cases e : val32 s.mem B M (nw len) = 1
  · have e' := e
    rw [expanded] at e'
    have low : w32 s.mem B M = 1 := by omega
    have high : val32 s.mem B (M + 4) (nw len - 1) = 0 := by omega
    have lo : s.mem.readW (off B M) 32 = 1 := BitVec.eq_of_toNat_eq low
    rw [ite_eq_left e, ite_eq_left e, lo, high]; rfl
  · have or0 : ∀ x : BitVec 32, x ||| 0 = x := fun _ => BitVec.or_zero
    rw [ite_eq_right e, ite_eq_right e, or0, expanded]

end VG.Proof.Rsa.X86.InvBatchRt
