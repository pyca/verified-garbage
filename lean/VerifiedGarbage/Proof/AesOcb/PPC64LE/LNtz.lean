module

public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# AES-OCB on PPC64LE: `L_{ntz(i)}` (`lNtz`)

Untrusted: everything here is checked by Lean. `lNtz` copies `L_0` to
`W + lO` and doubles it while the block index `i` (in `r26`), shifted right
once more each time (in `r12`), is even: `ntz(i)` times (`lNtz_ok`). The
invariant: after `j` doublings, `W + lO` holds `L_j`, `r12` is `i / 2^j`,
which is positive, and `ntz(i) = j + ntz(i / 2^j)`. As on AArch64
(`Proof/AesOcb/AArch64/LNtz.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Ocb (Block blockAtMem double lAt ntz)
open VG.Proof.AesGcm.PPC64LE (eval_zero)
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_li → cwp_li, wp_and → cwp_and, wp_lsr → cwp_lsr,
  wp_or → cwp_or

theorem toNat_lt {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hv

theorem and1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (v % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, toNat_lt hv, show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.and_one_is_mod,
    toNat_lt (by omega)]

theorem shr1 {v : Nat} (hv : v < 2 ^ 64) : BitVec.ofNat 64 v >>> 1 = BitVec.ofNat 64 (v / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_lt hv, toNat_lt (by omega), Nat.shiftRight_eq_div_pow]

/-- The registers `lNtz` writes. -/
abbrev ntzRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r12]

/-- What `lNtz` leaves. -/
structure LNtzPost (W : Addr) (l : Block) (i : Nat) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s'.mem
  val : blockAtMem s'.mem (W + BitVec.ofNat 64 lO) = lAt l (ntz i)
  gpr : ∀ r, r ∉ ntzRegs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- A step that keeps memory and writes the registers `rs` alone. -/
structure Regs (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `r5 ← r12 ∧ 1`, for `r12 = v`. -/
theorem low1_ok {s : State} {v : Nat} (hv : v < 2 ^ 64) (h12 : s.gpr .r12 = BitVec.ofNat 64 v) :
    WP isa (.block low1) s fun s' => s'.gpr .r5 = BitVec.ofNat 64 (v % 2) ∧ s'.gpr .r12 = BitVec.ofNat 64 v ∧
      Regs [.r0, .r5] s s' := by
  unfold low1
  refine cwp_li (by decide) fun s₁ u₁ => cwp_and fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), h12, and1 hv]
  · rw [u₂.other _ (by decide), u₁.other _ (by decide), h12]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₂.other _ hr.2, u₁.other _ hr.1]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.sp, u₁.sp]
  · rw [u₂.lr, u₁.lr]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]

/-- The doubling loop, from `L_a` with `r12 = i / 2^a` even. -/
theorem lNtzLoop_ok {W : Addr} {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {l : Block}
    {i a : Nat} (hi' : i < 2 ^ 64) (hpos : 0 < i / 2 ^ a) (he : i / 2 ^ a % 2 = 0)
    (hntz : ntz i = a + ntz (i / 2 ^ a)) (h12 : s.gpr .r12 = BitVec.ofNat 64 (i / 2 ^ a))
    (hl : blockAtMem s.mem (W + BitVec.ofNat 64 lO) = lAt l a) :
    WP isa (.loop (.block (dbl .r31 lO lO ++ ([.lsr .d .r12 .r12 1] : List Instr) ++ low1)) (.zero .d .r5)) s
      (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.PPC64LE.in_off hw h (by decide)
  refine WP.loop (M := isa)
    (fun (k : Nat) (t : State) => ∃ j, k = i / 2 ^ j ∧ 0 < i / 2 ^ j ∧ i / 2 ^ j % 2 = 0 ∧
      ntz i = j + ntz (i / 2 ^ j) ∧ t.gpr .r12 = BitVec.ofNat 64 (i / 2 ^ j) ∧
      Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t.mem ∧ blockAtMem t.mem (W + BitVec.ofNat 64 lO) = lAt l j ∧
      (∀ r, r ∉ ntzRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
    (i / 2 ^ a) _ ⟨a, rfl, hpos, he, hntz, h12, Frame.refl _ _, hl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rintro k t ⟨j, rfl, hpos, hev, hntz, x12, fr, v, g, sp, lr, rd, wr⟩
  have hv : i / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi'
  have h31t : t.gpr .r31 = W := by rw [g _ (by decide), h31]
  have e : i / 2 ^ (j + 1) = i / 2 ^ j / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  refine WP.block_append (WP.block_append (WP.mono (dbl_ok (s := t) (b := .r31) (a := lO) (d := lO) (by decide)
    (by decide) h31t h31t (by decide) (by rw [rd, wr]; exact Proof.AesGcm.PPC64LE.in_left (wW (by decide)))
    (by rw [rd, wr]; exact Proof.AesGcm.PPC64LE.in_left (wW (by decide)))
    (by rw [wr]; exact wW (by decide)) (by rw [wr]; exact wW (by decide))) fun t₁ D₁ => ?_))
  have x12₁ : t₁.gpr .r12 = BitVec.ofNat 64 (i / 2 ^ j) := by rw [D₁.gpr _ (by decide), x12]
  refine cwp_lsr (by decide) fun t₂ u₂ => WP.block_nil ?_
  have x12₂ : t₂.gpr .r12 = BitVec.ofNat 64 (i / 2 ^ (j + 1)) := by rw [u₂.gpr, x12₁, shr1 hv, e]
  refine WP.mono (low1_ok (by omega) x12₂) fun t₃ ⟨x5₃, x12₃, R₃⟩ => ?_
  have fr' : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem t₃.mem := by
    rw [R₃.mem, u₂.mem]
    exact fun x hx => (D₁.frame x hx).trans (fr x hx)
  have v' : blockAtMem t₃.mem (W + BitVec.ofNat 64 lO) = lAt l (j + 1) := by
    rw [R₃.mem, u₂.mem, D₁.val, v]; rfl
  have g' : ∀ r, r ∉ ntzRegs → t₃.gpr r = s.gpr r := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₃.gpr r (by simp [hr.1, hr.2.2.2.1]), u₂.other _ hr.2.2.2.2.2,
      D₁.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]),
      g r (by simp [ntzRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  have sp' : t₃.sp = s.sp := by rw [R₃.sp, u₂.sp, D₁.sp, sp]
  have lr' : t₃.lr = s.lr := by rw [R₃.lr, u₂.lr, D₁.lr, lr]
  have rd' : t₃.rd = s.rd := by rw [R₃.rd, u₂.rd, D₁.rd, rd]
  have wr' : t₃.wr = s.wr := by rw [R₃.wr, u₂.wr, D₁.wr, wr]
  have hntz' : ntz i = (j + 1) + ntz (i / 2 ^ (j + 1)) := by
    rw [hntz, Proof.Ocb.ntz_even hpos hev, e]; omega
  by_cases hodd : i / 2 ^ (j + 1) % 2 = 0
  · right
    refine ⟨(eval_zero x5₃ (by omega)).trans (by simp [hodd]), i / 2 ^ (j + 1), by rw [e]; omega, j + 1, rfl,
      by rw [e]; omega, hodd, hntz', x12₃, fr', v', g', sp', lr', rd', wr'⟩
  · left
    refine ⟨(eval_zero x5₃ (by omega)).trans (by simp [hodd]), ⟨fr', ?_, g', sp', lr', rd', wr'⟩⟩
    rw [v', hntz', Proof.Ocb.ntz_odd (by omega)]

theorem lNtz_ok {W : Addr} {s : State} (h31 : s.gpr .r31 = W) (hw : Covers [⟨W, 2560⟩] s.wr) {l : Block} {i : Nat}
    (hi : 0 < i) (hi' : i < 2 ^ 64) (h26 : s.gpr .r26 = BitVec.ofNat 64 i)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa lNtz s (LNtzPost W l i s) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.PPC64LE.in_off hw h (by decide)
  unfold lNtz
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (copy16_ok (s := s) (a := l0O) (d := lO) (by decide)
    (by decide) h31 (Proof.AesGcm.PPC64LE.in_left (wW (by decide)))
    (Proof.AesGcm.PPC64LE.in_left (wW (by decide))) (wW (by decide)) (wW (by decide))) fun s₁ B₁ => ?_)))
  refine cwp_or fun s₁' u₁' => WP.block_nil ?_
  have x12₁' : s₁'.gpr .r12 = BitVec.ofNat 64 i := by
    rw [u₁'.gpr, BitVec.or_self, B₁.gpr _ (by decide), h26]
  refine WP.mono (low1_ok hi' x12₁') fun s₂ ⟨x5₂, x12₂, R₂⟩ => ?_
  have g₂ : ∀ r, r ∉ ntzRegs → s₂.gpr r = s.gpr r := fun r hr => by
    simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R₂.gpr r (by simp [hr.1, hr.2.2.2.1]), u₁'.other _ hr.2.2.2.2.2, B₁.gpr r (by simp [hr.2.1, hr.2.2.1])]
  have fr₂ : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem s₂.mem := by rw [R₂.mem, u₁'.mem]; exact B₁.frame
  have v₂ : blockAtMem s₂.mem (W + BitVec.ofNat 64 lO) = lAt l 0 := by rw [R₂.mem, u₁'.mem, B₁.val, hl0]
  have sp₂ : s₂.sp = s.sp := by rw [R₂.sp, u₁'.sp, B₁.sp]
  have lr₂ : s₂.lr = s.lr := by rw [R₂.lr, u₁'.lr, B₁.lr]
  have rd₂ : s₂.rd = s.rd := by rw [R₂.rd, u₁'.rd, B₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [R₂.wr, u₁'.wr, B₁.wr]
  have h31₂ : s₂.gpr .r31 = W := by rw [g₂ _ (by decide), h31]
  refine WP.ite (decide (i % 2 = 0)) (eval_zero x5₂ (by omega)) (fun hb => ?_)
    (fun hb => WP.block_nil ⟨fr₂, ?_, g₂, sp₂, lr₂, rd₂, wr₂⟩)
  · have he : i % 2 = 0 := of_decide_eq_true hb
    exact WP.mono (lNtzLoop_ok h31₂ (by rw [wr₂]; exact hw) hi' (a := 0) (by simpa using hi) (by simpa using he)
      (by simp) (by simpa using x12₂) v₂) fun t P =>
        ⟨fr₂.trans P.frame, P.val, fun r hr => (P.gpr r hr).trans (g₂ r hr), P.sp.trans sp₂, P.lr.trans lr₂,
          P.rd.trans rd₂, P.wr.trans wr₂⟩
  · rw [v₂, Proof.Ocb.ntz_odd (by simp at hb; omega)]

end VG.Proof.AesOcb.PPC64LE
