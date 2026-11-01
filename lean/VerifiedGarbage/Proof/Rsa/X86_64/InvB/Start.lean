module

public import VerifiedGarbage.Proof.Rsa.X86_64.InvB.Batch
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Rsa.Ranges

/-!
# RSA's inverse by divsteps on x86-64: the start

Clearing, copying and setting arrays up to 25 (`zeroAI_ok`, `copyAI_ok`,
`setOneAI_ok`, as `Pieces.lean`'s for the first 16), and the start of the
inverse (`start_ok`): `m` with its low bit set in `aP` and `f`, `g` the input
plus `m` if it is even, `(a, b) = (0, 1)`, `d = 1`, `-m⁻¹ mod 2^64`, and `rdi`
at the window.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem zeroAI_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z) {j : Nat}
    (hj : j < 26) :
    WP isa (zeroA j) s fun t =>
      wv t.mem B (slot w j) (w + 2) = 0 ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        Keep [.r12, .r9, .r8, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) hZ
  unfold zeroA
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base_ok j (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_))
  refine WP.mono (zeroAccLoop_ok (h.scr.congr (k₁.trans k₂).2.2) h8 ((k₂.gpr (by decide)).trans h12)
    (by have := h.w1; omega_arith) (by have := h.w2; omega_arith) (by omega_arith)) fun t ⟨hz, o, k₃⟩ => ?_
  rw [m₂, m₁] at o
  exact ⟨hz, o, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem copyAI_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z) {o a : Nat}
    (ho : o < 26) (ha : a < 26) (hoa : o ≠ a) :
    WP isa (copyA o a) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w a) w ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧
        Keep [.r12, .r9, .rsi, .rbx, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have so : slot w o + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt ho) hZ
  have sa : slot w a + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt ha) hZ
  have sp := slot_far (w := w) hoa
  unfold copyA
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok a o (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hsi, hbx, m₂, k₂⟩ => ?_))
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (copyWords_ok hsi hbx ((k₂.gpr (by decide)).trans h12) (by have := h.w1; omega_arith)
    (by have := h.w2; omega_arith) (by omega_arith) (fun i hi => hs₂.ld (by omega_arith)) (fun i hi => hs₂.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun t ⟨hv, _, o', k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  exact ⟨hv, o', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem setOneAI_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z) {j : Nat}
    (hj : j < 26) :
    WP isa (.block (setOneA j)) s fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64) ∧ Keep [.r12, .r9, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) hZ
  unfold setOneA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.st (d := slot w j) (by omega), m₂, m₁]
    rfl) rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `setOdd`: `m`'s low bit set. -/
theorem setOdd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z) :
    WP isa (.block setOdd) s fun t =>
      t.mem = s.mem.writeW (off B (slot w aP)) (word s.mem B (slot w aP) ||| BitVec.signExtend 64 (1 : BitVec 32)) ∧
        Keep [.r12, .r9, .r8, .rax] s t := by
  have hn := h.scr.nowrap
  have sj : slot w aP + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt (show aP < 26 by decide)) hZ
  unfold setOdd
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aP (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (slot w aP))
      (word s.mem B (slot w aP) ||| BitVec.signExtend 64 (1 : BitVec 32))) (by
    xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w aP) (by omega), hs₂.st (d := slot w aP) (by omega), m₂, m₁]
    done) rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem mask_even (x : BitVec 64) :
    (x &&& (1 : BitVec 64)) - (1 : BitVec 64) = mask (decide (x.toNat % 2 = 0)) := by
  have h2 : x &&& (1 : BitVec 64) = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod,
      BitVec.toNat_ofNat]
    omega
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- `gInit`: `[g] = (m if [t]₀ is even) + [t]` over `w + 1` words. -/
theorem gInit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z) :
    WP isa (seqs gInit) s fun t => ∃ c : Bool,
      wv t.mem B (slot w aG) (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat =
        (if (word s.mem B (slot w aT)).toNat % 2 = 0 then wv s.mem B (slot w aP) (w + 1) else 0) +
          wv s.mem B (slot w aT) (w + 1) ∧
      Outside B (slot w aG) (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .rbx, .rbp, .r8, .r9, .r10, .r12, .r14, .r15] s t := by
  have hn := h.scr.nowrap
  have e20 := slot_eq w 20; have e23 := slot_eq w 23; have e25 := slot_eq w 25; have e26 := slot_eq w 26
  have hw := h.w1
  have hw' := h.w2
  simp only [gInit, seqs]
  have hb : WP isa (.block (ws ++ base aT .r8 ++ ([.mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1),
      .alu .sub .rax (.imm 1), .mov .r15 (.reg .rax), .alu .add .r12 (.imm 1), .mov32 .rbp (.imm 0)] : List Instr) ++
      base aG .rbx ++ base aP .r10)) s fun t =>
      t.gpr .r8 = off B (slot w aT) ∧ t.gpr .rbx = off B (slot w aG) ∧ t.gpr .r10 = off B (slot w aP) ∧
      t.gpr .r15 = mask (decide ((word s.mem B (slot w aT)).toNat % 2 = 0)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.rax, .rbx, .rbp, .r8, .r9, .r10, .r12, .r15] s t := by
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
    have di₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
    rw [WP.block_append_iff]
    refine WP.mono (base_ok aT (r := .r8) (by decide) di₁ h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
    rw [WP.block_append_iff]
    have hs₂ := h.scr.congr (k₁.trans k₂).2.2
    refine WP.mono (WP.keep [.rax, .r15, .r12, .rbp] (Q := fun t =>
        t.gpr .r15 = mask (decide ((word s.mem B (slot w aT)).toNat % 2 = 0)) ∧
        t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧ t.gpr .rbp = mask false ∧ t.mem = s₂.mem) (by
      xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, (k₂.gpr (by decide)).trans h12,
        hs₂.ld (d := slot w aT) (by unfold aT; omega), m₂, m₁]
      exact ⟨mask_even _, by rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]⟩) rfl)
      fun s₃ ⟨⟨r15₃, r12₃, bp₃, m₃⟩, k₃⟩ => ?_
    have h9₃ : s₃.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := ((k₂.trans k₃).gpr (by decide)).trans h9
    have di₃ : s₃.gpr .rdi = B := ((k₂.trans k₃).gpr (by decide)).trans di₁
    refine WP.mono (base2_ok aG aP (r₁ := .rbx) (r₂ := .r10) (by decide) (by decide) (by decide) di₃ h9₃ (by decide))
      fun t ⟨bx, b10, mt, kt⟩ => ⟨(kt.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h8), bx, b10,
        (kt.gpr (by decide)).trans r15₃, (kt.gpr (by decide)).trans r12₃, (kt.gpr (by decide)).trans bp₃,
        by rw [mt, m₃, m₂, m₁], (((k₁.trans k₂).trans k₃).trans kt).mono (by decide)⟩
  refine WP.seq (WP.mono hb fun s₁ ⟨r8₁, bx₁, r10₁, r15₁, r12₁, bp₁, m₁, k₁⟩ => ?_)
  refine WP.mono (addM_ok (h.scr.congr k₁.2.2) bx₁ r10₁ r8₁ r15₁ r12₁ bp₁ (by omega) (by omega)
    (by unfold aG; omega) (by unfold aP; omega) (by unfold aT; omega) (by unfold aP aG; omega)
    (by unfold aT aG; omega)) fun t ⟨c, _, hv, ho, kt⟩ => ⟨c, ?_, by rw [← m₁]; exact ho, (k₁.trans kt).mono (by decide)⟩
  rw [hv, m₁]
  by_cases he : (word s.mem B (slot w aT)).toNat % 2 = 0 <;> simp [he]

/-- `setup`: `-m⁻¹ mod 2^64` and `d = 1` into the window, `r15 := n`, `rsi := 3 n + 2`, `rdi` to the window. -/
theorem setup_ok {s : State} {B : Addr} {Z w n : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (hodd : (word s.mem B (slot w aP)).toNat % 2 = 1) :
    WP isa (.block setup) s fun t => ∃ mi : BitVec 64,
      ((word s.mem B (slot w aP)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧
      t.mem = (s.mem.writeW (off B (slot w 16 + oMi)) mi).writeW (off B (slot w 16 + oD)) (1 : BitVec 64) ∧
      t.gpr .rdi = off B (slot w 16) ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧ t.gpr .rsi = BitVec.ofNat 64 (3 * n + 2) ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r12, .r15] s t := by
  have hn' := h.scr.nowrap
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e25 := slot_eq w 25; have e26 := slot_eq w 26
  have hw := h.w1
  unfold setup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  have di₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans h.rdi
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aP (r := .r8) (by decide) di₁ h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  rw [show ∀ l : List Instr, ([Instr.mov .rbx (.mem (at0 .r8))] ++ l) = [Instr.mov .rbx (.mem (at0 .r8))] ++ l
    from fun _ => rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = word s.mem B (slot w aP) ∧ t.mem = s₂.mem) (by
    xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.ld (d := slot w aP) (by unfold aP; omega), m₂, m₁]) rfl) fun s₃ ⟨⟨bx₃, m₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (minv_ok s₃ (by rw [bx₃]; exact hodd)) fun s₄ ⟨hm₄, k₄, m₄⟩ => ?_
  rw [bx₃] at hm₄
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have di₄ : s₄.gpr .rdi = B := (k14.gpr (by decide)).trans h.rdi
  have h9₄ : s₄.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (((k₂.trans k₃).trans k₄).gpr (by decide)).trans h9
  rw [WP.block_append_iff]
  refine WP.mono (base_ok aWin (r := .r8) (by decide) di₄ h9₄) fun s₅ ⟨h8₅, m₅, k₅⟩ => ?_
  have hs₅ := h.scr.congr (k14.trans k₅).2.2
  have r15₅ := s₅.gpr .r15
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r15, .rsi] (Q := fun t =>
      t.mem = (s₅.mem.writeW (off B (slot w 16 + oMi)) (s₄.gpr .r15)).writeW (off B (slot w 16 + oD)) (1 : BitVec 64) ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧ t.gpr .rsi = BitVec.ofNat 64 (3 * n + 2)) (by
    unfold aWin at h8₅
    xrun [State.ea, h8₅, offD, (k₅.gpr (by decide) : s₅.gpr .r15 = s₄.gpr .r15),
      (k14.trans k₅).gpr (by decide) |>.trans h13,
      hs₅.st (d := slot w 16 + oMi) (by unfold oMi; omega), hs₅.st (d := slot w 16 + oD) (by unfold oD; omega)]
    refine ⟨rfl, ?_⟩
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
      BitVec.ofNat_add_ofNat]
    congr 1; omega) rfl) fun s₆ ⟨⟨m₆, r15₆, rsi₆⟩, k₆⟩ => ?_
  have k16 := (k14.trans k₅).trans k₆
  refine WP.mono (base_ok aWin (r := .rdi) (by decide) ((k16.gpr (by decide)).trans h.rdi)
    (((k₅.trans k₆).gpr (by decide)).trans h9₄)) fun t ⟨di, mt, kt⟩ => ⟨s₄.gpr .r15, hm₄, ?_, di,
      (kt.gpr (by decide)).trans (((k₅.trans k₆).gpr (by decide)).trans h9₄), (kt.gpr (by decide)).trans r15₆,
      (kt.gpr (by decide)).trans rsi₆, (k16.trans kt).mono (by decide)⟩
  rw [mt, m₆, m₅, m₄, m₃, m₂, m₁]

end VG.Proof.Rsa.X86_64.InvB
