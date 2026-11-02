module
-- separate module: the inverse's proof is split in a chain of modules, so that a change rebuilds only the modules after it

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

/-- `wsR`: `r12 := w` from the stride in `r9`. -/
theorem wsR_ok {s : State} {w : Nat} (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (hw : w < 2 ^ 24) :
    WP isa (.block wsR) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem ∧
        Keep [.r12] s t := by
  refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
    t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨a, b, c⟩, k⟩ => ⟨a, b, c, k⟩
  unfold wsR
  xrun [h9]
  apply BitVec.eq_of_toNat_eq
  have h8 : 8 * (w + 2) < 2 ^ 64 := by omega
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h8, show (2 : BitVec 64).toNat = 2 from rfl]
  omega

theorem zeroAI_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) {j : Nat} (hj : j < 26) :
    WP isa (zeroI j) s fun t =>
      wv t.mem B (slot w j) (w + 2) = 0 ∧ Outside B (slot w j) (8 * (w + 2)) s.mem t.mem ∧
        t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧ Keep [.r12, .r8, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) hZ
  unfold zeroI
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsR_ok h9 h.w2) fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base_ok j (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_))
  refine WP.mono (zeroAccLoop_ok (h.scr.congr (k₁.trans k₂).2.2) h8 ((k₂.gpr (by decide)).trans h12)
    (by have := h.w1; omega_arith) (by have := h.w2; omega_arith) (by omega_arith)) fun t ⟨hz, o, k₃⟩ => ?_
  rw [m₂, m₁] at o
  exact ⟨hz, o, ((k₂.trans k₃).gpr (by decide)).trans h9, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem copyAI_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) {o a : Nat} (ho : o < 26) (ha : a < 26) (hoa : o ≠ a) :
    WP isa (copyI o a) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w a) w ∧ Outside B (slot w o) (8 * w) s.mem t.mem ∧
        Keep [.r12, .rsi, .rbx, .rax, .r14] s t := by
  have hn := h.scr.nowrap
  have so : slot w o + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt ho) hZ
  have sa : slot w a + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt ha) hZ
  have sp := slot_far (w := w) hoa
  unfold copyI
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsR_ok h9 h.w2) fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok a o (r₁ := .rsi) (r₂ := .rbx) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨hsi, hbx, m₂, k₂⟩ => ?_))
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (copyWords_ok hsi hbx ((k₂.gpr (by decide)).trans h12) (by have := h.w1; omega_arith)
    (by have := h.w2; omega_arith) (by omega_arith) (fun i hi => hs₂.ld (by omega_arith)) (fun i hi => hs₂.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off B (by omega_arith)]; omega_arith)) fun t ⟨hv, _, o', k₃⟩ => ?_
  rw [m₂, m₁] at hv o'
  exact ⟨hv, o', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

theorem setOneAI_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) {j : Nat} (hj : j < 26) :
    WP isa (.block (setOneI j)) s fun t =>
      t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64) ∧ Keep [.r12, .rbx, .rax] s t := by
  have hn := h.scr.nowrap
  have sj : slot w j + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt hj) hZ
  unfold setOneI
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsR_ok h9 h.w2) fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok j (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j)) (1 : BitVec 64)) (by
    xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hs₂.st (d := slot w j) (by omega), m₂, m₁]
    rfl) rfl) fun t ⟨mt, k₃⟩ => ⟨mt, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `setOdd`: `m`'s low bit set. -/
theorem setOdd_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block setOdd) s fun t =>
      t.mem = s.mem.writeW (off B (slot w aP)) (word s.mem B (slot w aP) >>> 1 + word s.mem B (slot w aP) >>> 1 +
        BitVec.signExtend 64 (1 : BitVec 32)) ∧
        Keep [.r12, .r8, .rax] s t := by
  have hn := h.scr.nowrap
  have sj : slot w aP + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_lt (show aP < 26 by decide)) hZ
  unfold setOdd
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsR_ok h9 h.w2) fun s₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aP (r := .r8) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨h8, m₂, k₂⟩ => ?_
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem.writeW (off B (slot w aP))
      (word s.mem B (slot w aP) >>> 1 + word s.mem B (slot w aP) >>> 1 + BitVec.signExtend 64 (1 : BitVec 32))) (by
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
theorem gInit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (seqs gInit) s fun t => ∃ c : Bool,
      wv t.mem B (slot w aG) (w + 1) + 2 ^ (64 * (w + 1)) * c.toNat =
        (if (word s.mem B (slot w aT)).toNat % 2 = 0 then wv s.mem B (slot w aP) (w + 1) else 0) +
          wv s.mem B (slot w aT) (w + 1) ∧
      Outside B (slot w aG) (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .rbx, .rbp, .r8, .r10, .r12, .r14, .r15] s t := by
  have hn := h.scr.nowrap
  have e20 := slot_eq w 20; have e23 := slot_eq w 23; have e25 := slot_eq w 25; have e26 := slot_eq w 26
  have hw := h.w1
  have hw' := h.w2
  simp only [gInit, seqs]
  have hb : WP isa (.block (wsR ++ base aT .r8 ++ ([.mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1),
      .alu .sub .rax (.imm 1), .mov .r15 (.reg .rax), .alu .add .r12 (.imm 1), .mov32 .rbp (.imm 0)] : List Instr) ++
      base aG .rbx ++ base aP .r10)) s fun t =>
      t.gpr .r8 = off B (slot w aT) ∧ t.gpr .rbx = off B (slot w aG) ∧ t.gpr .r10 = off B (slot w aP) ∧
      t.gpr .r15 = mask (decide ((word s.mem B (slot w aT)).toNat % 2 = 0)) ∧
      t.gpr .r12 = BitVec.ofNat 64 (w + 1) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem ∧
      Keep [.rax, .rbx, .rbp, .r8, .r10, .r12, .r15] s t := by
    simp only [List.append_assoc]
    rw [WP.block_append_iff]
    refine WP.mono (wsR_ok h9 h.w2) fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
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
    (h9' : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (hodd : (word s.mem B (slot w aP)).toNat % 2 = 1) :
    WP isa (.block setup) s fun t => ∃ mi : BitVec 64,
      ((word s.mem B (slot w aP)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 ∧
      t.mem = (s.mem.writeW (off B (slot w 16 + oMi)) mi).writeW (off B (slot w 16 + oD)) (1 : BitVec 64) ∧
      t.gpr .rdi = off B (slot w 16) ∧ t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .r15 = BitVec.ofNat 64 n ∧ t.gpr .rsi = BitVec.ofNat 64 (3 * n + 2) ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .r8, .r12, .r15] s t := by
  have hn' := h.scr.nowrap
  have e16 := slot_eq w 16; have e19 := slot_eq w 19; have e25 := slot_eq w 25; have e26 := slot_eq w 26
  have hw := h.w1
  unfold setup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (wsR_ok h9' h.w2) fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
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

/-! ### The start as a whole -/

/-- An array apart from one that changed. -/
theorem out_arr {m m' : Mem} {B : Addr} {w j k K L : Nat} (o : Outside B (slot w j) L m m') (hjk : j ≠ k)
    (hL : L ≤ 8 * (w + 2)) (hK : K ≤ w + 2) (hn : slot w k + 8 * (w + 2) ≤ 2 ^ 64) :
    wv m' B (slot w k) K = wv m B (slot w k) K :=
  o.wv (by have := slot_far (w := w) hjk; omega) (by omega)

/-- `Ws` after a change to an array. -/
theorem wsOut {s t : State} {B : Addr} {Z w j L : Nat} (h : Ws s B Z w) (o : Outside B (slot w j) L s.mem t.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : Ws t B Z w :=
  h.congr (rs := [(slot w j, L)]) (Frm.of_outside o (List.mem_singleton.mpr rfl))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w j L) k hr

/-- A number of `w + 2` words whose top two are zero and below `2^(64 k)`. -/
theorem wv_top0 {m : Mem} {B : Addr} {e w k : Nat} (hk : k ≤ w + 2) (h0 : word m B (e + 8 * w) = 0)
    (h1 : word m B (e + 8 * w + 8) = 0) (hv : wv m B e w < 2 ^ (64 * k)) : wv m B e k = wv m B e w := by
  have e2 : wv m B e (w + 2) = wv m B e w := by rw [wv_top2, h0, h1]; rfl
  rw [wv_low_of_lt hk (by rw [e2]; exact hv), e2]

/-- The words of a number that is zero. -/
theorem wv_zero_word {m : Mem} {p : Addr} {e : Nat} : ∀ {N : Nat}, wv m p e N = 0 → ∀ i < N, word m p (e + 8 * i) = 0
  | 0, _, i, hi => absurd hi (by omega)
  | N + 1, h, i, hi => by
    rw [wv] at h
    have hp : 0 < 2 ^ (64 * N) := Nat.two_pow_pos _
    have h0 := Nat.eq_zero_of_add_eq_zero h
    by_cases hiN : i = N
    · subst hiN
      have h2 := (Nat.mul_eq_zero.mp h0.2).resolve_left (by omega)
      exact BitVec.eq_of_toNat_eq (by simp [h2])
    · exact wv_zero_word h0.1 i (by omega)

/-- `m` with its low bit set. -/
def pOf (m : Nat) : Nat := if m % 2 = 1 then m else m + 1

theorem odd_word (x : BitVec 64) :
    ((x >>> 1) + (x >>> 1) + BitVec.signExtend 64 (1 : BitVec 32)).toNat =
      x.toNat + (if x.toNat % 2 = 0 then 1 else 0) := by
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    show (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 from rfl]
  split <;> omega

/-- `copyA o a` onto a cleared array: all `w + 2` words. -/
theorem copy_full {m m' : Mem} {B : Addr} {w o a : Nat} (hv : wv m' B (slot w o) w = wv m B (slot w a) w)
    (h0 : wv m B (slot w o) (w + 2) = 0) (ho : Outside B (slot w o) (8 * w) m m')
    (hn : slot w o + 8 * (w + 2) ≤ 2 ^ 64) : wv m' B (slot w o) (w + 2) = wv m B (slot w a) w := by
  have z0 : word m B (slot w o + 8 * w) = 0 ∧ word m B (slot w o + 8 * w + 8) = 0 := by
    rw [wv_top2] at h0
    have a := (word m B (slot w o + 8 * w)).isLt
    have b := (word m B (slot w o + 8 * w + 8)).isLt
    have := Nat.eq_zero_of_add_eq_zero h0
    have hp : 0 < 2 ^ (64 * w) := Nat.two_pow_pos _
    have h2 := (Nat.mul_eq_zero.mp this.2).resolve_left (by omega)
    exact ⟨BitVec.eq_of_toNat_eq (by simp; omega), BitVec.eq_of_toNat_eq (by simp; omega)⟩
  rw [wv_top2, hv, ho.word (by omega) (by omega), ho.word (by omega) (by omega), z0.1, z0.2]; rfl

theorem mul_one_cong {p q mi M : Nat} (h : p % M = q % M) : (p * mi + 1) % M = (q * mi + 1) % M := by
  rw [Nat.add_mod, Nat.mul_mod, h, ← Nat.mul_mod, ← Nat.add_mod]

theorem wv_lowK {m : Mem} {B : Addr} {e w K v : Nat} (h : wv m B e (w + 2) = v) (hv : v < 2 ^ (64 * K))
    (hK : K ≤ w + 2) : wv m B e K = v :=
  (wv_low_of_lt hK (by rw [h]; exact hv)).trans h

/-- The start: the batches' state for `invRunS 59 p mi x 0`, `p = pOf m`, `x` the input
plus `p` if it is even. -/
theorem start_ok {s : State} {B : Addr} {Z w n iU iM : Nat} (h : Ws s B Z w) (hZ : slot w 26 ≤ Z)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) (hU : iU < 16) (hM : iM < 16)
    (hu : wv s.mem B (slot w iU) w < 2 ^ (64 * n)) (hm : wv s.mem B (slot w iM) w < 2 ^ (64 * n)) :
    WP isa (seqs (start iU iM)) s fun t => ∃ mi : Nat,
      BS B Z w n (pOf (wv s.mem B (slot w iM) w)) mi
        ⟨1, pOf (wv s.mem B (slot w iM) w),
          ((if wv s.mem B (slot w iU) w % 2 = 0 then pOf (wv s.mem B (slot w iM) w) else 0) +
            wv s.mem B (slot w iU) w : Nat), 0, 1⟩ t ∧
      (pOf (wv s.mem B (slot w iM) w) * mi + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aP) (n + 1) = pOf (wv s.mem B (slot w iM) w) ∧
      t.gpr .rsi = BitVec.ofNat 64 (3 * n + 2) ∧
      Frm B [(slot w 16, 80 * (w + 2))] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r12, .r14, .r15] s t := by
  have hN := h.scr.nowrap
  have hw1 := h.w1; have hw24 := h.w2
  have sl : ∀ j, j < 26 → slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_lt hj) hZ
  have hS := sl 25 (by decide)
  have eF : slot w aF = 256 + 19 * (8 * (w + 2)) := slot_eq w 19
  have eG : slot w aG = 256 + 20 * (8 * (w + 2)) := slot_eq w 20
  have eA : slot w aA = 256 + 21 * (8 * (w + 2)) := slot_eq w 21
  have eB : slot w aB = 256 + 22 * (8 * (w + 2)) := slot_eq w 22
  have eT : slot w aT = 256 + 23 * (8 * (w + 2)) := slot_eq w 23
  have eP : slot w aP = 256 + 25 * (8 * (w + 2)) := slot_eq w 25
  have eW : slot w 16 = 256 + 16 * (8 * (w + 2)) := slot_eq w 16
  rw [show start iU iM = ([zeroI aF, zeroI aG, zeroI aA, zeroI aB, zeroI aT, zeroI aS, zeroI aP, copyI aP iM,
    .block setOdd, copyI aF aP, copyI aT iU] ++ gInit) ++ [.block (setOneI aB), .block setup] from rfl,
    seqs_append_iff _ _ (by simp) (by simp), seqs_append_iff _ _ (by simp) (by simp [gInit])]
  simp only [seqs]
  refine WP.seq (WP.mono (zeroAI_ok h hZ h9 (j := aF) (by decide)) fun s₁ ⟨zF₁, o₁, r9₁, k₁⟩ => ?_)
  have h₁ := wsOut h o₁ k₁ (by decide)
  refine WP.seq (WP.mono (zeroAI_ok h₁ hZ r9₁ (j := aG) (by decide)) fun s₂ ⟨zG₂, o₂, r9₂, k₂⟩ => ?_)
  have h₂ := wsOut h₁ o₂ k₂ (by decide)
  refine WP.seq (WP.mono (zeroAI_ok h₂ hZ r9₂ (j := aA) (by decide)) fun s₃ ⟨zA₃, o₃, r9₃, k₃⟩ => ?_)
  have h₃ := wsOut h₂ o₃ k₃ (by decide)
  refine WP.seq (WP.mono (zeroAI_ok h₃ hZ r9₃ (j := aB) (by decide)) fun s₄ ⟨zB₄, o₄, r9₄, k₄⟩ => ?_)
  have h₄ := wsOut h₃ o₄ k₄ (by decide)
  refine WP.seq (WP.mono (zeroAI_ok h₄ hZ r9₄ (j := aT) (by decide)) fun s₅ ⟨zT₅, o₅, r9₅, k₅⟩ => ?_)
  have h₅ := wsOut h₄ o₅ k₅ (by decide)
  refine WP.seq (WP.mono (zeroAI_ok h₅ hZ r9₅ (j := aS) (by decide)) fun s₆ ⟨_, o₆, r9₆, k₆⟩ => ?_)
  have h₆ := wsOut h₅ o₆ k₆ (by decide)
  refine WP.seq (WP.mono (zeroAI_ok h₆ hZ r9₆ (j := aP) (by decide)) fun s₇ ⟨zP₇, o₇, r9₇, k₇⟩ => ?_)
  have h₇ := wsOut h₆ o₇ k₇ (by decide)
  have hU' : slot w iU + 8 * (w + 2) ≤ 2 ^ 64 := by have := sl iU (by omega); omega
  have hM' : slot w iM + 8 * (w + 2) ≤ 2 ^ 64 := by have := sl iM (by omega); omega
  have ar : ∀ j, j < 26 → slot w j + 8 * (w + 2) ≤ 2 ^ 64 := fun j hj => by have := sl j hj; omega
  -- The values after the clearing.
  have tr := fun {m m' : Mem} {j k K L : Nat} (o : Outside B (slot w j) L m m') (hjk : j ≠ k)
    (hL : L ≤ 8 * (w + 2)) (hK : K ≤ w + 2) (hk : k < 26) =>
    out_arr (K := K) o hjk hL hK (ar k hk)
  have zF₇ : wv s₇.mem B (slot w aF) (w + 2) = 0 := by
    rw [tr o₇ (by decide) (by omega) (by omega) (by decide), tr o₆ (by decide) (by omega) (by omega) (by decide),
      tr o₅ (by decide) (by omega) (by omega) (by decide), tr o₄ (by decide) (by omega) (by omega) (by decide),
      tr o₃ (by decide) (by omega) (by omega) (by decide), tr o₂ (by decide) (by omega) (by omega) (by decide), zF₁]
  have zG₇ : wv s₇.mem B (slot w aG) (w + 2) = 0 := by
    rw [tr o₇ (by decide) (by omega) (by omega) (by decide), tr o₆ (by decide) (by omega) (by omega) (by decide),
      tr o₅ (by decide) (by omega) (by omega) (by decide), tr o₄ (by decide) (by omega) (by omega) (by decide),
      tr o₃ (by decide) (by omega) (by omega) (by decide), zG₂]
  have zA₇ : wv s₇.mem B (slot w aA) (w + 2) = 0 := by
    rw [tr o₇ (by decide) (by omega) (by omega) (by decide), tr o₆ (by decide) (by omega) (by omega) (by decide),
      tr o₅ (by decide) (by omega) (by omega) (by decide), tr o₄ (by decide) (by omega) (by omega) (by decide), zA₃]
  have zB₇ : wv s₇.mem B (slot w aB) (w + 2) = 0 := by
    rw [tr o₇ (by decide) (by omega) (by omega) (by decide), tr o₆ (by decide) (by omega) (by omega) (by decide),
      tr o₅ (by decide) (by omega) (by omega) (by decide), zB₄]
  have zT₇ : wv s₇.mem B (slot w aT) (w + 2) = 0 := by
    rw [tr o₇ (by decide) (by omega) (by omega) (by decide), tr o₆ (by decide) (by omega) (by omega) (by decide), zT₅]
  have iU₇ : wv s₇.mem B (slot w iU) w = wv s.mem B (slot w iU) w := by
    rw [tr o₇ (by simp only [aP]; omega) (by omega) (by omega) (by omega), tr o₆ (by simp only [aS]; omega) (by omega) (by omega) (by omega),
      tr o₅ (by simp only [aT]; omega) (by omega) (by omega) (by omega), tr o₄ (by simp only [aB]; omega) (by omega) (by omega) (by omega),
      tr o₃ (by simp only [aA]; omega) (by omega) (by omega) (by omega), tr o₂ (by simp only [aG]; omega) (by omega) (by omega) (by omega),
      tr o₁ (by simp only [aF]; omega) (by omega) (by omega) (by omega)]
  have iM₇ : wv s₇.mem B (slot w iM) w = wv s.mem B (slot w iM) w := by
    rw [tr o₇ (by simp only [aP]; omega) (by omega) (by omega) (by omega), tr o₆ (by simp only [aS]; omega) (by omega) (by omega) (by omega),
      tr o₅ (by simp only [aT]; omega) (by omega) (by omega) (by omega), tr o₄ (by simp only [aB]; omega) (by omega) (by omega) (by omega),
      tr o₃ (by simp only [aA]; omega) (by omega) (by omega) (by omega), tr o₂ (by simp only [aG]; omega) (by omega) (by omega) (by omega),
      tr o₁ (by simp only [aF]; omega) (by omega) (by omega) (by omega)]
  -- `m` into `aP`, made odd.
  refine WP.seq (WP.mono (copyAI_ok h₇ hZ r9₇ (o := aP) (a := iM) (by decide) (by omega) (by simp only [aP]; omega))
    fun s₈ ⟨vP₈, o₈, k₈⟩ => ?_)
  have h₈ := wsOut h₇ o₈ k₈ (by decide)
  have r9₈ : s₈.gpr .r9 = _ := (k₈.gpr (by decide)).trans r9₇
  have P₈ := copy_full vP₈ zP₇ o₈ (ar aP (by decide))
  rw [iM₇] at P₈
  refine WP.seq (WP.mono (setOdd_ok h₈ hZ r9₈) fun s₉ ⟨m₉, k₉⟩ => ?_)
  have o₉ : Outside B (slot w aP) 8 s₈.mem s₉.mem := by rw [m₉]; exact writeW_outside _ _ _ (by have := ar aP (by decide); omega)
  have h₉ := wsOut h₈ o₉ k₉ (by decide)
  have r9₉ : s₉.gpr .r9 = _ := (k₉.gpr (by decide)).trans r9₈
  have pw := odd_word (word s₈.mem B (slot w aP))
  have eP₈ := P₈
  rw [show w + 2 = (w + 1) + 1 from rfl, wv_succ_low] at eP₈
  have hpar : (word s₈.mem B (slot w aP)).toNat % 2 = wv s.mem B (slot w iM) w % 2 := by omega
  have hp_lt : pOf (wv s.mem B (slot w iM) w) < 2 ^ (64 * n) := by
    unfold pOf; split
    · exact hm
    · have : 2 ^ (64 * n) = 2 * 2 ^ (64 * n - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      omega
  have P₉ : wv s₉.mem B (slot w aP) (w + 2) = pOf (wv s.mem B (slot w iM) w) := by
    rw [show w + 2 = (w + 1) + 1 from rfl, wv_succ_low, m₉, word_writeW_self,
      (writeW_outside s₈.mem B _ (d := slot w aP) (by have := ar aP (by decide); omega)).wv (Or.inr (by omega))
        (by have := ar aP (by decide); omega), pw]
    unfold pOf
    by_cases hm2 : wv s.mem B (slot w iM) w % 2 = 1
    · simp only [show ¬ ((word s₈.mem B (slot w aP)).toNat % 2 = 0) by omega, hm2, ↓reduceIte]; omega
    · simp only [show (word s₈.mem B (slot w aP)).toNat % 2 = 0 by omega, hm2, ↓reduceIte]; omega
  have hpw : pOf (wv s.mem B (slot w iM) w) < 2 ^ (64 * w) :=
    Nat.lt_of_lt_of_le hp_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have Pw₉ : wv s₉.mem B (slot w aP) w = pOf (wv s.mem B (slot w iM) w) :=
    (wv_low_of_lt (show w ≤ w + 2 by omega) (by rw [P₉]; exact hpw)).trans P₉
  -- `f := m`, `t := a`.
  refine WP.seq (WP.mono (copyAI_ok h₉ hZ r9₉ (o := aF) (a := aP) (by decide) (by decide) (by decide))
    fun s₁₀ ⟨vF₁₀, o₁₀, k₁₀⟩ => ?_)
  have h₁₀ := wsOut h₉ o₁₀ k₁₀ (by decide)
  have r9₁₀ : s₁₀.gpr .r9 = _ := (k₁₀.gpr (by decide)).trans r9₉
  have F₁₀ := copy_full vF₁₀ (by rw [tr o₉ (by decide) (by omega) (by omega) (by decide),
    tr o₈ (by decide) (by omega) (by omega) (by decide), zF₇]) o₁₀ (ar aF (by decide))
  rw [Pw₉] at F₁₀
  refine WP.mono (copyAI_ok h₁₀ hZ r9₁₀ (o := aT) (a := iU) (by decide) (by omega) (by simp only [aT]; omega))
    fun s₁₁ ⟨vT₁₁, o₁₁, k₁₁⟩ => ?_
  have h₁₁ := wsOut h₁₀ o₁₁ k₁₁ (by decide)
  have r9₁₁ : s₁₁.gpr .r9 = _ := (k₁₁.gpr (by decide)).trans r9₁₀
  have T₁₁ := copy_full vT₁₁ (by rw [tr o₁₀ (by decide) (by omega) (by omega) (by decide),
    tr o₉ (by decide) (by omega) (by omega) (by decide), tr o₈ (by decide) (by omega) (by omega) (by decide), zT₇])
    o₁₁ (ar aT (by decide))
  rw [tr o₁₀ (by simp only [aF]; omega) (by omega) (by omega) (by omega),
    tr o₉ (by simp only [aP]; omega) (by omega) (by omega) (by omega),
    tr o₈ (by simp only [aP]; omega) (by omega) (by omega) (by omega), iU₇] at T₁₁
  have P₁₁ : wv s₁₁.mem B (slot w aP) (w + 2) = pOf (wv s.mem B (slot w iM) w) := by
    rw [tr o₁₁ (by decide) (by omega) (by omega) (by decide), tr o₁₀ (by decide) (by omega) (by omega) (by decide), P₉]
  have hpw1 : pOf (wv s.mem B (slot w iM) w) < 2 ^ (64 * (w + 1)) :=
    Nat.lt_of_lt_of_le hp_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hu1 : wv s.mem B (slot w iU) w < 2 ^ (64 * (w + 1)) :=
    Nat.lt_of_lt_of_le hu (Nat.pow_le_pow_right (by decide) (by omega))
  have P1₁₁ : wv s₁₁.mem B (slot w aP) (w + 1) = pOf (wv s.mem B (slot w iM) w) :=
    (wv_low_of_lt (show w + 1 ≤ w + 2 by omega) (by rw [P₁₁]; exact hpw1)).trans P₁₁
  have T1₁₁ : wv s₁₁.mem B (slot w aT) (w + 1) = wv s.mem B (slot w iU) w :=
    (wv_low_of_lt (show w + 1 ≤ w + 2 by omega) (by rw [T₁₁]; exact hu1)).trans T₁₁
  have eT₁ := T₁₁
  rw [show w + 2 = (w + 1) + 1 from rfl, wv_succ_low] at eT₁
  have tpar : (word s₁₁.mem B (slot w aT)).toNat % 2 = wv s.mem B (slot w iU) w % 2 := by omega
  -- `g := a + (m if a is even)`.
  refine WP.mono (gInit_ok h₁₁ hZ r9₁₁) fun s₁₂ ⟨c, vG₁₂, o₁₂, k₁₂⟩ => ?_
  have h₁₂ := wsOut h₁₁ o₁₂ k₁₂ (by decide)
  have r9₁₂ : s₁₂.gpr .r9 = _ := (k₁₂.gpr (by decide)).trans r9₁₁
  rw [P1₁₁, T1₁₁, tpar] at vG₁₂
  have hx : (if wv s.mem B (slot w iU) w % 2 = 0 then pOf (wv s.mem B (slot w iM) w) else 0) +
      wv s.mem B (slot w iU) w < 2 ^ (64 * n) * 2 := by split <;> omega
  have hx1 : 2 ^ (64 * n) * 2 ≤ 2 ^ (64 * (n + 1)) := by rw [pow64_succ]; exact Nat.mul_le_mul_left _ (by decide)
  have hxw : 2 ^ (64 * (n + 1)) ≤ 2 ^ (64 * (w + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : c = false := by
    cases c
    · rfl
    · have := wv_lt s₁₂.mem B (slot w aG) (w + 1)
      simp at vG₁₂; omega
  subst hc
  simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at vG₁₂
  have zG₁₁ : wv s₁₁.mem B (slot w aG) (w + 2) = 0 := by
    rw [tr o₁₁ (by decide) (by omega) (by omega) (by decide), tr o₁₀ (by decide) (by omega) (by omega) (by decide),
      tr o₉ (by decide) (by omega) (by omega) (by decide), tr o₈ (by decide) (by omega) (by omega) (by decide), zG₇]
  have z1 : word s₁₂.mem B (slot w aG + 8 * (w + 1)) = 0 := by
    rw [o₁₂.word (by omega) (by have := ar aG (by decide); omega)]
    exact wv_zero_word zG₁₁ (w + 1) (by omega)
  have G₁₂ : wv s₁₂.mem B (slot w aG) (w + 2) = (if wv s.mem B (slot w iU) w % 2 = 0 then
      pOf (wv s.mem B (slot w iM) w) else 0) + wv s.mem B (slot w iU) w := by
    rw [show w + 2 = (w + 1) + 1 from rfl, wv, z1, vG₁₂]; rfl
  -- `b := 1`.
  show WP isa (.seq (.block (setOneI aB)) (.block setup)) s₁₂ _
  have zB₁₂ : wv s₁₂.mem B (slot w aB) (w + 2) = 0 := by
    rw [tr o₁₂ (by decide) (by omega) (by omega) (by decide), tr o₁₁ (by decide) (by omega) (by omega) (by decide),
      tr o₁₀ (by decide) (by omega) (by omega) (by decide), tr o₉ (by decide) (by omega) (by omega) (by decide),
      tr o₈ (by decide) (by omega) (by omega) (by decide), zB₇]
  refine WP.seq (WP.mono (setOneAI_ok h₁₂ hZ r9₁₂ (j := aB) (by decide)) fun s₁₃ ⟨m₁₃, k₁₃⟩ => ?_)
  have o₁₃ : Outside B (slot w aB) 8 s₁₂.mem s₁₃.mem := by
    rw [m₁₃]; exact writeW_outside _ _ _ (by have := ar aB (by decide); omega)
  have h₁₃ := wsOut h₁₂ o₁₃ k₁₃ (by decide)
  have r9₁₃ : s₁₃.gpr .r9 = _ := (k₁₃.gpr (by decide)).trans r9₁₂
  have B₁₃ : wv s₁₃.mem B (slot w aB) (w + 2) = 1 := by
    rw [show w + 2 = (w + 1) + 1 from rfl, wv_succ_low, m₁₃, word_writeW_self,
      (writeW_outside s₁₂.mem B _ (d := slot w aB) (by have := ar aB (by decide); omega)).wv (Or.inr (by omega))
        (by have := ar aB (by decide); omega)]
    have := zB₁₂
    rw [show w + 2 = (w + 1) + 1 from rfl, wv_succ_low] at this
    have h0 := Nat.eq_zero_of_add_eq_zero this
    have h2 := (Nat.mul_eq_zero.mp h0.2).resolve_left (by decide)
    rw [h2]; rfl
  -- The odd modulus' low word.
  have wP₁₃ : word s₁₃.mem B (slot w aP) = word s₉.mem B (slot w aP) := by
    rw [o₁₃.word (by omega) (by have := ar aP (by decide); omega),
      o₁₂.word (by omega) (by have := ar aP (by decide); omega),
      o₁₁.word (by omega) (by have := ar aP (by decide); omega),
      o₁₀.word (by omega) (by have := ar aP (by decide); omega)]
  have wP₉ : (word s₉.mem B (slot w aP)).toNat = (word s₈.mem B (slot w aP)).toNat +
      (if (word s₈.mem B (slot w aP)).toNat % 2 = 0 then 1 else 0) := by
    rw [m₉, word_writeW_self, pw]
  have hodd : (word s₁₃.mem B (slot w aP)).toNat % 2 = 1 := by rw [wP₁₃, wP₉]; split <;> omega
  have r13₁₃ : s₁₃.gpr .r13 = BitVec.ofNat 64 n := by
    rw [k₁₃.gpr (by decide), k₁₂.gpr (by decide), k₁₁.gpr (by decide), k₁₀.gpr (by decide), k₉.gpr (by decide),
      k₈.gpr (by decide), k₇.gpr (by decide), k₆.gpr (by decide), k₅.gpr (by decide), k₄.gpr (by decide),
      k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
    exact h13
  refine WP.mono (setup_ok h₁₃ hZ r9₁₃ r13₁₃ hodd) fun t ⟨mi, hmi, mt, dit, r9t, r15t, rsit, kt⟩ => ?_
  have oD' : slot w 16 + oD + 8 ≤ 2 ^ 64 := by unfold oD; omega
  have oMi' : slot w 16 + oMi + 8 ≤ 2 ^ 64 := by unfold oMi; omega
  have oW₁ : Outside B (slot w 16 + oMi) 8 s₁₃.mem (s₁₃.mem.writeW (off B (slot w 16 + oMi)) mi) :=
    writeW_outside _ _ _ oMi'
  have oW₂ : Outside B (slot w 16 + oD) 8 (s₁₃.mem.writeW (off B (slot w 16 + oMi)) mi) t.mem := by
    rw [mt]; exact writeW_outside _ _ _ oD'
  have wa : ∀ k, 19 ≤ k → k < 26 → ∀ K, K ≤ w + 2 → wv t.mem B (slot w k) K = wv s₁₃.mem B (slot w k) K := by
    intro k hk hk' K hK
    have ek := slot_eq w k
    have hk₁ := ar k hk'
    have hk₂ : 19 * (8 * (w + 2)) ≤ k * (8 * (w + 2)) := Nat.mul_le_mul_right _ hk
    rw [oW₂.wv (Or.inr (by unfold oD; omega)) (by omega), oW₁.wv (Or.inr (by unfold oMi; omega)) (by omega)]
  have hx2 : ((if wv s.mem B (slot w iU) w % 2 = 0 then pOf (wv s.mem B (slot w iM) w) else 0) +
      wv s.mem B (slot w iU) w) < 2 ^ (64 * (n + 1)) := by omega
  have hp1 : pOf (wv s.mem B (slot w iM) w) < 2 ^ (64 * (n + 1)) :=
    Nat.lt_of_lt_of_le hp_lt (Nat.pow_le_pow_right (by decide) (by omega))
  have hone : 1 < 2 ^ (64 * (n + 1)) := Nat.one_lt_two_pow (by omega)
  have Pt : ∀ K, K ≤ w + 2 → wv t.mem B (slot w aP) K = wv s₉.mem B (slot w aP) K := fun K hK => by
    rw [wa aP (by decide) (by decide) K hK, tr o₁₃ (by decide) (by omega) hK (by decide),
      tr o₁₂ (by decide) (by omega) hK (by decide), tr o₁₁ (by decide) (by omega) hK (by decide),
      tr o₁₀ (by decide) (by omega) hK (by decide)]
  have hr : (word s₁₃.mem B (slot w aP)).toNat = pOf (wv s.mem B (slot w iM) w) % 2 ^ 64 := by
    rw [wP₁₃, ← wv_mod64 _ _ _ (n := w + 2) (by omega), P₉]
  have fr : ∀ {m m' : Mem} {o L : Nat}, Outside B o L m m' → slot w 16 ≤ o → o + L ≤ slot w 16 + 80 * (w + 2) →
      Frm B [(slot w 16, 80 * (w + 2))] m m' := fun ho h1 h2 =>
    fun x hx => ho x (by have := hx _ (List.mem_singleton.mpr rfl); dsimp only at this; omega)
  have eS : slot w aS = 256 + 24 * (8 * (w + 2)) := slot_eq w 24
  refine ⟨mi.toNat, BS.mk (h₁₃.scr.congr kt.2.2) dit r9t r15t ?cD ?cMi ?cP ?cF ?cG ?cA ?cB, ?hm, ?P1, rsit, ?frm, ?keep⟩
  case cD => rw [mt, word_writeW_self]; rfl
  case cMi => rw [oW₂.word (Or.inr (by unfold oMi oD; omega)) oMi', word_writeW_self]
  case cP => show wv t.mem B (slot w aP) n = _; rw [Pt n (by omega)]; exact wv_lowK P₉ hp_lt (by omega)
  case P1 => rw [Pt (n + 1) (by omega)]; exact wv_lowK P₉ hp1 (by omega)
  case cF =>
    show (wv t.mem B (slot w aF) (n + 1) : Int) % _ = _
    rw [wa aF (by decide) (by decide) _ (by omega), tr o₁₃ (by decide) (by omega) (by omega) (by decide),
      tr o₁₂ (by decide) (by omega) (by omega) (by decide), tr o₁₁ (by decide) (by omega) (by omega) (by decide),
      wv_lowK F₁₀ hp1 (by omega)]
  case cG =>
    show (wv t.mem B (slot w aG) (n + 1) : Int) % _ = _
    rw [wa aG (by decide) (by decide) _ (by omega), tr o₁₃ (by decide) (by omega) (by omega) (by decide),
      wv_lowK G₁₂ hx2 (by omega)]
  case cA =>
    show (wv t.mem B (slot w aA) (n + 1) : Int) % _ = _
    have zA : wv s₁₃.mem B (slot w aA) (w + 2) = 0 := by
      rw [tr o₁₃ (by decide) (by omega) (by omega) (by decide), tr o₁₂ (by decide) (by omega) (by omega) (by decide),
        tr o₁₁ (by decide) (by omega) (by omega) (by decide), tr o₁₀ (by decide) (by omega) (by omega) (by decide),
        tr o₉ (by decide) (by omega) (by omega) (by decide), tr o₈ (by decide) (by omega) (by omega) (by decide), zA₇]
    rw [wa aA (by decide) (by decide) _ (by omega), wv_lowK zA (Nat.two_pow_pos _) (by omega)]; rfl
  case cB =>
    show (wv t.mem B (slot w aB) (n + 1) : Int) % _ = _
    rw [wa aB (by decide) (by decide) _ (by omega), wv_lowK B₁₃ hone (by omega)]; rfl
  case hm => rw [hr] at hmi; rw [mul_one_cong (Nat.mod_mod _ _).symm]; exact hmi
  case frm =>
    have := ar 25 (by decide)
    refine (fr o₁ (by omega) (by omega)).trans <| (fr o₂ (by omega) (by omega)).trans <|
      (fr o₃ (by omega) (by omega)).trans <| (fr o₄ (by omega) (by omega)).trans <|
      (fr o₅ (by omega) (by omega)).trans <| (fr o₆ (by omega) (by omega)).trans <|
      (fr o₇ (by omega) (by omega)).trans <| (fr o₈ (by omega) (by omega)).trans <|
      (fr o₉ (by omega) (by omega)).trans <| (fr o₁₀ (by omega) (by omega)).trans <|
      (fr o₁₁ (by omega) (by omega)).trans <| (fr o₁₂ (by omega) (by omega)).trans <|
      (fr o₁₃ (by omega) (by omega)).trans <| (fr oW₁ (by unfold oMi; omega) (by unfold oMi; omega)).trans
        (fr oW₂ (by unfold oD; omega) (by unfold oD; omega))
  case keep =>
    exact (((((((((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).trans k₈).trans k₉).trans
      k₁₀).trans k₁₁).trans k₁₂).trans k₁₃).trans kt).mono (by decide)

end VG.Proof.Rsa.X86_64.InvB
