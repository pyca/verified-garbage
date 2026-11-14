module

public import VerifiedGarbage.Impl.Dsa.Arm.Arith
public import VerifiedGarbage.Proof.Dsa.Arm.Pow
public import VerifiedGarbage.Proof.Dsa.Arm.Stream
public import VerifiedGarbage.Proof.Dsa.Arm.ContextCall
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Dsa.Arm.PowCall
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.Arm.Arith`, which only this module used -/

section

/-!
# DSA's reductions and products as functions on 32-bit ARM: their code

`vg_dsa_mulmod_{n}` and `vg_dsa_reduce_{n}` (`Impl/Dsa/Arm/Arith.lean`) save
the registers they use as `vg_dsa_pow_{n}_{e}` does (`save_ok`), set up the
context, run `ordinaryMul` or `reduceStream`, and restore the registers
(`restore_ok`): `mulBody_ok`, `reduceBody_ok`. Their contracts in this file's
terms are `mulK` and `reduceK`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow VG.Impl.Dsa.Arm.Arith
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr wp_dp op2_reg dpVal)

/-- The registers saved in the header, with `r12` the working space. -/
theorem save_ok {s : State} {base : Addr} {size : Nat} (E : Entry s base size) (hz : 44 ≤ size) :
    WP isa (.block save) s fun t => Ws t base size ∧
      (∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧
      Outs base (words slots) s.mem t.mem ∧ Rest [.r12] s t := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun s₁ u₁ => ?_
  have w₁ : Ws s₁ base size := ⟨by rw [u₁.gpr]; exact E.wb, u₁.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (stores_ok slots w₁ (slots_fit hz) slots_apart) fun t ⟨S, O, R⟩ =>
    ⟨w₁.of_rest R (by decide), fun x hx => by rw [S x hx, u₁.other _ (slots_r12 x hx)],
      by rw [← u₁.mem]; exact O, (u₁.rest (by decide)).trans (R.mono (by decide))⟩

/-- The saved registers, from the header. -/
theorem restore_ok {s t : State} {base : Addr} {size : Nat} (hs : Ws t base size) (hz : 44 ≤ size)
    (hv : ∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) :
    WP isa (.block restore) t fun u =>
      (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ Rest preserved t u ∧ u.mem = t.mem := by
  refine WP.mono (loads_ok slots hs (slots_fit hz) slots_r12 slots_nodup) fun u ⟨L, R, M⟩ =>
    ⟨fun r hr => ?_, slots_regs ▸ R, M⟩
  rw [← slots_regs] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  rw [L x hx, hv x hx]

/-- The saved words, through code that changes only `rs`, apart from them. -/
theorem saved_keep {s t u : State} {base : Addr} {rs : List (Nat × Nat)}
    (hv : ∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) (O : Outs base rs t.mem u.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ 8 ∨ 48 ≤ r.1) :
    ∀ x ∈ slots, u.mem.readW (off base x.2) 32 = s.gpr x.1 := fun x hx => by
  have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
  simp only at hw
  rw [outs_readW O (fun r h => by have := hr r h; omega_arith) (by omega_arith), hv x hx]

theorem setup_apart (n : Nat) : ∀ r ∈ Context.callRanges n, r.1 + r.2 ≤ 8 ∨ 48 ≤ r.1 := by
  simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    slot, stride]
  omega_arith

theorem stream_apart (n : Nat) : ∀ r ∈ streamRanges n, r.1 + r.2 ≤ 8 ∨ 48 ≤ r.1 := by
  simp only [streamRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    slot, stride]
  omega_arith

theorem stream_scratch {n : Nat} :
    ∀ r ∈ streamRanges n, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [streamRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      contextBytes, slot, stride]
    omega_arith)

theorem ctx_of_rest {n m size : Nat} {base : Addr} {rs : List Reg} {s t : State} (h : Context n m base size s)
    (R : Rest rs s t) (h12 : .r12 ∉ rs) (hm : t.mem = s.mem) : Context n m base size t :=
  ⟨h.ws.of_rest R h12, h.size_le, h.small, h.n0, by rw [hm]; exact h.modulus, h.gt_one, by rw [hm]; exact h.inverse⟩

/-! ## Products -/

/-- `a b mod m` into slot 9, for the modulus in slot 0 and `a`, `b` in slots
8 and 11; the registers the calling convention keeps are restored. -/
theorem mulBody_ok {s : State} {base : Addr} {size n m : Nat} (E : Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (mulBody n) s fun t =>
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) * val32 s.mem base (slot n 11) (2 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have nw := E.nowrap
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have s8 := slot_bound (n := n) (i := 8) (by decide)
  have s11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have h8 := slot_header n 8
  have h11 := slot_header n 11
  simp only [stride] at s0 s8 s11
  unfold mulBody
  refine WP.seq (WP.mono (save_ok E (by omega_arith)) fun s₂ ⟨w₂, S₂, O₂, R₂⟩ => ?_)
  have away : ∀ {d k : Nat}, 48 ≤ d → d + 4 * k ≤ 2 ^ 64 → val32 s₂.mem base d k = val32 s.mem base d k :=
    fun hd hd' => O₂.val32 (fun r hr => .inr (by have := slots_words r hr; omega_arith)) hd'
  have hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [away (by omega_arith) (by omega_arith)]; exact hv
  refine WP.seq (WP.mono (Context.call_ok w₂ (by omega_arith) hn hn48 hv₂ hm1 hodd)
    fun s₃ ⟨c₃, _, rr₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (ordinaryMul_ok c₃ rr₃) fun s₄ ⟨c₄, V₄, O₄, R₄⟩ => ?_)
  refine WP.mono (restore_ok c₄.ws (by omega_arith) (saved_keep (saved_keep S₂ O₃ (setup_apart n)) O₄ (stream_apart n)))
    fun t ⟨P, R₅, M₅⟩ => ⟨?_, ?_, P, ?_, ?_, ?_⟩
  · have k₃ : ∀ {d k : Nat}, (∀ r ∈ Context.callRanges n, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 4 * k ≤ 2 ^ 64 →
        val32 s₃.mem base d k = val32 s₂.mem base d k := fun h h' => O₃.val32 h h'
    rw [M₅, V₄,
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      away (by omega_arith) (by omega_arith), away (by omega_arith) (by omega_arith), Nat.mul_comm]
  · rw [M₅]
    exact ((outs_within O₂ (words_scratch n)).trans (outs_within O₃ (setup_scratch hn))).trans
      (outs_within O₄ stream_scratch)
  · rw [R₅.sp, R₄.sp, R₃.sp, R₂.sp]
  · rw [R₅.rd, R₄.rd, R₃.rd, R₂.rd]
  · rw [R₅.wr, R₄.wr, R₃.wr, R₂.wr]

/-! ## Reductions -/

/-- Bytes apart from the context keep their values through code that
changes only ranges within it. -/
theorem bytes_apart {m m' : Mem} {base p : Addr} {len n : Nat} {rs : List (Nat × Nat)}
    (O : Outs base rs m m') (hd : Region.Disjoint ⟨p, len⟩ ⟨base, contextBytes n⟩) (hl : len ≤ 2 ^ 64)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ contextBytes n) (hn48 : n ≤ 48) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len :=
  VG.Proof.Dsa.outs_bytes O hl (fun r h => by have := hr r h; have := contextBytes_bounds hn48; omega_arith)
    fun r h => hd.sub_right (Offset.sub_base base (hr r h))

theorem setup_inside {n : Nat} (hn : 0 < n) : ∀ r ∈ Context.callRanges n, r.1 + r.2 ≤ contextBytes n := by
  simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    contextBytes, slot, stride]
  omega_arith

/-- The saves, then the bytes' address into `r11` and their length into the
header. -/
theorem reduceHead_ok {s : State} {base : Addr} {size : Nat} (E : Entry s base size) (hz : 48 ≤ size) :
    WP isa (.block (save ++ ([.mov .r11 (.reg .r2), .str .r3 .r12 lenAt] : List Instr))) s fun t => Ws t base size ∧
      (∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧
      Outs base ((lenAt, 4) :: words slots) s.mem t.mem ∧ Rest [.r11, .r12] s t ∧
      t.gpr .r11 = s.gpr .r2 ∧ t.mem.readW (off base lenAt) 32 = s.gpr .r3 := by
  have nw := E.nowrap
  refine VG.Proof.X25519.Arm.WP.append (save_ok E (by omega_arith)) fun s₁ ⟨w₁, S₁, O₁, R₁⟩ =>
    wp_mov (op2_reg s₁ .r2) fun s₂ u₂ => ?_
  have w₂ := w₁.of_upd u₂ (by decide)
  refine wp_str (by decide) (w₂.ea12 (by simp only [lenAt]; omega_arith)) (w₂.write (by simp only [lenAt]; omega_arith))
    fun t m₃ => WP.block_nil ⟨w₂.of_mupd m₃, fun x hx => ?_, ?_, ?_, ?_, ?_⟩
  · have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    simp only at hw
    rw [m₃.mem, Mem.readW_writeW_sep (Offset.sep base (.inl (by simp only [lenAt]; omega_arith)) (by omega_arith)
      (by simp only [lenAt]; omega_arith)) (by decide), u₂.mem]
    exact S₁ x hx
  · rw [m₃.mem]
    refine (O₁.mono fun r h => List.mem_cons_of_mem _ h).trans ?_
    rw [u₂.mem]
    exact Outs.of_outside (writeW32_outside _ _ _ (by simp only [lenAt]; omega_arith)) (List.mem_cons_self ..)
  · exact ((R₁.mono (by decide)).trans (u₂.rest (by decide))).trans (m₃.rest _)
  · rw [m₃.gpr, u₂.gpr, R₁.gpr .r2 (by decide)]
  · rw [m₃.mem, Mem.readW_writeW_self32, u₂.other .r3 (by decide), R₁.gpr .r3 (by decide)]

/-- `lr` = the header's length plus `r11`. -/
theorem reduceEnd_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 48 ≤ size) :
    WP isa (.block [.ldr .lr .r12 lenAt, .dp .add .lr .lr (.reg .r11)]) s fun t =>
      t.gpr .lr = s.mem.readW (off base lenAt) 32 + s.gpr .r11 ∧ Rest [.lr] s t ∧ t.mem = s.mem :=
  wp_ldr (by decide) (hs.ea12 (by simp only [lenAt]; omega_arith)) (hs.read (by simp only [lenAt]; omega_arith))
    fun u₁ v₁ => wp_dp (op2_reg _ _) fun t v₂ => WP.block_nil
      ⟨by rw [v₂.gpr, dpVal, v₁.gpr, v₁.other .r11 (by decide)],
        (v₁.rest (by decide)).trans (v₂.rest (by decide)), by rw [v₂.mem, v₁.mem]⟩

theorem len_apart : ∀ r ∈ (lenAt, 4) :: words slots, r.1 + r.2 ≤ 64 := by decide

/-- The `len` bytes at `p`, in `r2` and `r3`, apart from the context, reduced
modulo the modulus in slot 0, into slot 9; the registers the calling
convention keeps are restored. -/
theorem reduceBody_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32} (E : Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm : 255 < m) (hodd : m % 2 = 1)
    (hp : s.gpr .r2 = p) (hl : (s.gpr .r3).toNat = len) (hfit : p.toNat + len ≤ 2 ^ 32)
    (hr : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    WP isa (reduceBody n) s fun t =>
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have c48 : 48 ≤ contextBytes n := by simp only [contextBytes, slot, stride]; omega_arith
  have nw := E.nowrap
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at s0
  have llt : len < 2 ^ 32 := by rw [← hl]; exact (s.gpr .r3).isLt
  unfold reduceBody
  refine WP.seq (WP.mono (reduceHead_ok E (by omega_arith)) fun s₂ ⟨w₂, S₂, O₂, R₂, P₂, L₂⟩ => ?_)
  have hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (fun r hr => .inr (by have := len_apart r hr; omega_arith)) (by omega_arith)]; exact hv
  refine WP.seq (WP.mono (Context.light_ok w₂ (by omega_arith) hn hn48 hv₂ (by omega_arith) hodd)
    fun s₃ ⟨c₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (reduceEnd_ok c₃.ws (by omega_arith)) fun s₄ ⟨L₄, R₄, M₄⟩ => ?_)
  have c₄ := ctx_of_rest c₃ R₄ (by decide) M₄
  have r11 : s₄.gpr .r11 = p := by rw [R₄.gpr .r11 (by decide), R₃.gpr .r11 (by decide), P₂, hp]
  have lr : s₄.gpr .lr = p + BitVec.ofNat 32 len := by
    rw [L₄, R₃.gpr .r11 (by decide), P₂, hp, outs_readW O₃ (fun r h => by have := setup_apart n r h; simp only [lenAt]; omega_arith)
      (by simp only [lenAt]; omega_arith), L₂, BitVec.add_comm, ← hl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have rw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by
    rw [R₄.rd, R₄.wr, R₃.rd, R₃.wr, R₂.rd, R₂.wr]
  refine WP.seq (WP.mono (reduceStream_ok c₄ hm hfit llt r11 lr (fun i hi => by rw [rw₄]; exact hr i hi)
    (by rw [show off base 0 = base from BitVec.add_zero _]; exact hd)) fun s₅ ⟨c₅, V₅, O₅, R₅⟩ => ?_)
  have K₄ : Outs base [] s₃.mem s₄.mem := fun x _ => by rw [M₄]
  refine WP.mono (restore_ok c₅.ws (by omega_arith)
    (saved_keep (saved_keep (saved_keep S₂ O₃ (setup_apart n)) K₄ (by simp)) O₅ (stream_apart n)))
    fun t ⟨P, R₆, M₆⟩ => ⟨?_, ?_, P, ?_, ?_, ?_⟩
  · rw [M₆, V₅, M₄, bytes_apart O₃ hd (by omega_arith) (setup_inside hn) hn48,
      bytes_apart O₂ hd (by omega_arith) (fun r h => by have := len_apart r h; omega_arith) hn48]
  · rw [M₆]
    refine ((outs_within O₂ (within_scratch fun r h => .inl (len_apart r h))).trans
      (outs_within O₃ (setup_scratch hn))).trans ?_
    rw [← M₄]
    exact outs_within O₅ stream_scratch
  · rw [R₆.sp, R₅.sp, R₄.sp, R₃.sp, R₂.sp]
  · rw [R₆.rd, R₅.rd, R₄.rd, R₃.rd, R₂.rd]
  · rw [R₆.wr, R₅.wr, R₄.wr, R₃.wr, R₂.wr]

/-! ## The functions -/

/-- `vg_dsa_mulmod_{n}`'s contract in this file's terms, as `powK`. -/
def mulK (n : Nat) : Contract isa where
  pre := (powK n 1).pre
  post s t :=
    let base := State.addr (s.gpr .r0)
    val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) * val32 s.mem base (slot n 11) (2 * n) %
          val32 s.mem base (slot n 0) (2 * n) ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0

theorem mulK_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (mulK n).pre s) :
    ∃ tr t, Exec isa (mulBody n) s tr t ∧ abiPreserved s t ∧ (mulK n).post s t := by
  obtain ⟨-, hwr, hnw, hz, hodd, hm1⟩ := h
  have E : Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega_arith, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, ex, V, O, P, hsp, -, -⟩ := mulBody_ok E hz hn hn48 rfl hm1 hodd
  exact ⟨tr, t, ex, ⟨P, hsp⟩, V, O⟩

theorem mulK_ct (n : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (mulK n).pre (mulK n).pub (mulBody n) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ Eq => ?_
  have E : ∀ {s : State}, (mulK n).pre s → Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) := by
    intro s H
    exact ⟨rfl, ⟨_, Nat.le_refl _, by have := H.2.2.1; omega_arith, by rw [H.2.1]; simp⟩,
      by simpa only [VG.Proof.X25519.Arm.addr_toNat] using H.2.2.1⟩
  have E₂ : Entry s₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [Eq]; exact E h₂
  unfold mulBody
  refine savedSetup_trace (E h₁) E₂ h₁.2.2.2.1 h₂.2.2.2.1 hn hn48
    h₁.2.2.2.2.1 h₁.2.2.2.2.2 ?_ ?_ ?_
  · rw [Eq]; exact h₂.2.2.2.2.1
  · rw [Eq]; exact h₂.2.2.2.2.2
  · refine RelCT.seq (ordinaryMul_relCT n) ?_
    exact (relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
      fun _ _ _ => trivial

/-- `vg_dsa_reduce_{n}`'s contract in this file's terms: the working space at
`r0`, of `r1` words, and the `r3` bytes at `r2`, apart from it. -/
def reduceK (n : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (slot n 0) (2 * n)
    s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧
      Region.Disjoint ⟨base, (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ∧
      M % 2 = 1 ∧ 255 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    val32 t.mem base (slot n 9) (2 * n) =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) %
          val32 s.mem base (slot n 0) (2 * n) ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3

theorem reduceK_entry {n : Nat} {s : State} (h : (reduceK n).pre s) :
    Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
  ⟨rfl, ⟨_, Nat.le_refl _, by have := h.2.2.1; omega_arith, by rw [h.2.1]; exact List.mem_singleton_self _⟩,
    by rw [VG.Proof.X25519.Arm.addr_toNat]; exact h.2.2.1⟩

theorem reduceK_bytes {n : Nat} {s : State} (h : (reduceK n).pre s) :
    ∀ i < (s.gpr .r3).toNat, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 1 :=
  fun i hi => ⟨_, List.mem_append_left _ (by rw [h.1]; exact List.mem_singleton_self _),
    Offset.contains_base _ (by omega_arith) (by have := h.2.2.2.1; have := (s.gpr .r2).isLt; omega_arith)⟩

theorem reduceK_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (reduceK n).pre s) :
    ∃ tr t, Exec isa (reduceBody n) s tr t ∧ abiPreserved s t ∧ (reduceK n).post s t := by
  have E := reduceK_entry h
  have hb := reduceK_bytes h
  obtain ⟨-, -, -, hfit, hz, hd, hodd, hm⟩ := h
  obtain ⟨tr, t, ex, V, O, P, hsp, -, -⟩ := reduceBody_ok E hz hn hn48 rfl hm hodd rfl rfl hfit
    hb (hd.symm.sub_right (Region.sub_prefix hz))
  exact ⟨tr, t, ex, ⟨P, hsp⟩, V, O⟩

theorem addr_inj {a b : BitVec 32} (h : State.addr a = State.addr b) : a = b :=
  BitVec.eq_of_toNat_eq (by rw [← VG.Proof.X25519.Arm.addr_toNat a, ← VG.Proof.X25519.Arm.addr_toNat b, h])

theorem reduceK_ct (n : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (reduceK n).pre (reduceK n).pub (reduceBody n) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ ⟨p0, p2, p3⟩ => ?_
  have E₁ := reduceK_entry h₁
  have E₂ := reduceK_entry h₂
  have hz₁ := h₁.2.2.2.2.1
  have hz₂ := h₂.2.2.2.2.1
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have c48 : 48 ≤ contextBytes n := by simp only [contextBytes, slot, stride]; omega_arith
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at s0
  have pb : State.addr (s₁.gpr .r0) = State.addr (s₂.gpr .r0) := by rw [p0]
  unfold reduceBody
  refine SameTrace.seq (SameTrace.of_relCT (relCT_of_check (τ := VG.Arm.Taint.ofRegs [.r0, .r2, .r3])
      (σ := wsT true false) (h := .block []) (by decide))
      (VG.Arm.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> with_reducible assumption))
    (reduceHead_ok E₁ (by omega_arith)) (reduceHead_ok E₂ (by omega_arith))
    fun u₁ u₂ ⟨w₁, _, O₁, _, P₁, L₁⟩ ⟨w₂, _, O₂, _, P₂, L₂⟩ => ?_
  have mod : ∀ {s u : State} {base : Addr}, Outs base ((lenAt, 4) :: words slots) s.mem u.mem →
      val32 u.mem base (slot n 0) (2 * n) = val32 s.mem base (slot n 0) (2 * n) := fun O =>
    O.val32 (fun r hr => .inr (by have := len_apart r hr; omega_arith)) (by omega_arith)
  have W₂ : Ws u₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [pb]; exact w₂
  refine SameTrace.seq (Context.light_trace w₁ W₂ (by rw [P₁, P₂, p2]))
    (Context.light_ok w₁ (by omega_arith) hn hn48 (mod O₁) (by have := h₁.2.2.2.2.2.2.2; omega_arith)
      h₁.2.2.2.2.2.2.1)
    (Context.light_ok w₂ (by omega_arith) hn hn48 (mod O₂) (by have := h₂.2.2.2.2.2.2.2; omega_arith)
      h₂.2.2.2.2.2.2.1)
    fun v₁ v₂ ⟨c₁, Q₁, R₁⟩ ⟨c₂, Q₂, R₂⟩ => ?_
  refine SameTrace.seq (SameTrace.of_relCT (relCT_of_check (τ := wsT true false) (σ := wsT true false)
      (h := .block []) (by decide)) (VG.Arm.Taint.agree_ofRegs fun r hr => ?_))
    (reduceEnd_ok c₁.ws (by omega_arith)) (reduceEnd_ok c₂.ws (by omega_arith)) fun x₁ x₂ ⟨L₃, K₁, _⟩ ⟨L₄, K₂, _⟩ => ?_
  · simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact addr_inj (c₁.ws.wb.trans (pb.trans c₂.ws.wb.symm))
    · rw [R₁.gpr .r11 (by decide), R₂.gpr .r11 (by decide), P₁, P₂, p2]
  refine SameTrace.of_relCT (RelCT.seq (reduceStream_relCT n)
    ((relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
      fun _ _ _ => trivial)) (VG.Arm.Taint.agree_ofRegs fun r hr => ?_)
  have k : ∀ {s u : State} {base : Addr}, Outs base (Context.callRanges n) s.mem u.mem →
      u.mem.readW (off base lenAt) 32 = s.mem.readW (off base lenAt) 32 := fun O =>
    outs_readW O (fun r h => by have := setup_apart n r h; simp only [lenAt]; omega_arith) (by simp only [lenAt]; omega_arith)
  simp only [wsRegs, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [K₁.gpr .r12 (by decide), K₂.gpr .r12 (by decide)]
    exact addr_inj (c₁.ws.wb.trans (pb.trans c₂.ws.wb.symm))
  · rw [K₁.gpr .r11 (by decide), K₂.gpr .r11 (by decide), R₁.gpr .r11 (by decide), R₂.gpr .r11 (by decide),
      P₁, P₂, p2]
  · rw [L₃, L₄, R₁.gpr .r11 (by decide), R₂.gpr .r11 (by decide), P₁, P₂, p2, k Q₁, k Q₂, L₁, L₂, p3]

end VG.Proof.Dsa.Arm.Pow

end

end


/-!
# DSA's reductions and products as functions on 32-bit ARM: their calls

Calls of `vg_dsa_mulmod_{n}` and `vg_dsa_reduce_{n}` from code whose working
space is at `r12`, as `PowCall.lean` for `vg_dsa_pow_{n}_{e}`: the context's
bytes are the function's working space, which its contract narrows the call
to, with the reduction's bytes, and `r12` comes back from `r11`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Pow VG.Impl.Dsa.Arm.Arith
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_dp wp_movw op2_reg dpVal)

theorem mulBody_noFrames (n : Nat) : (mulBody n).noFrames = true := by
  simp only [mulBody, Impl.Dsa.Arm.Context.call, Impl.Dsa.Arm.Context.body, contextSetup, ordinaryMul, Dynamic.mul, rowD, digitRowD, mulRowD, csubD, Dynamic.zeros,
    ptrLoop, one, powerTwo, addD, addDigits, Code.noFrames, Bool.and_self]

theorem doubles_noCalls (n k : Nat) : (doubles n k).noCalls = true := by
  unfold doubles
  split <;> simp only [countedDouble, addDigits, csubD, ptrLoop, Code.noCalls, Bool.and_self]

theorem reduceBody_noFrames (n : Nat) : (reduceBody n).noFrames = true := by
  simp only [reduceBody, Impl.Dsa.Arm.Context.light, reduceStream, streamStep, reduceStep, addD, addDigits,
    csubD, Dynamic.zeros, ptrLoop, Code.noFrames, Bool.and_self, Bool.and_true, Bool.true_and]
  exact Code.noFrames_of_noCalls (doubles_noCalls n 8)

/-! ## Products -/

theorem mulCall_ok {s : State} {base : Addr} {size n m : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m)
    (hodd : m % 2 = 1) :
    WP isa (mulCall n) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) * val32 s.mem base (slot n 11) (2 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  unfold mulCall
  refine WP.seq (WP.mono (head_ok n) fun u ⟨h11, h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := mulK n) (mulK_correct hn hn48)
    (entry_pre (e := 1) hs hz hn48 h0 h1 M₁ (by rw [hv]; exact hodd) (by rw [hv]; exact hm1))
    (Covers.right (covers_ctx w₁ hz)) (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (mulBody_noFrames n))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  simp only [mulK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, M₁, hv] at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11]
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r11] := by revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

theorem mulCall_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n : Nat} (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁) (hz₂ : contextBytes n ≤ size₂)
    (hn : 0 < n) (hn48 : n ≤ 48)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 1 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 1 < val32 s₂.mem base (slot n 0) (2 * n)) :
    SameTrace isa (mulCall n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  unfold mulCall head
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs []) (c₀ := .block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (head_ok n) (head_ok n)
    fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, M₁⟩ ⟨_, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (mulK_correct hn hn48) (mulK_ct n hn hn48) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨entry_pre (e := 1) hs₁ hz₁ hn48 h0₁ h1₁ M₁ ho₁ hm₁, entry_pre (e := 1) hs₂ hz₂ hn48 h0₂ h1₂ M₂ ho₂ hm₂,
    ?_, Covers.right (covers_ctx w₁ hz₁), covers_ctx w₁ hz₁, Covers.right (covers_ctx w₂ hz₂), covers_ctx w₂ hz₂⟩
  simp only [mulK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
  exact BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat])

/-! ## Reductions -/

/-- The bytes' address and length. -/
theorem rpre_ok {s : State} :
    WP isa (.block [.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11)]) s fun u =>
      u.gpr .r2 = s.gpr .r11 ∧ u.gpr .r3 = s.gpr .lr - s.gpr .r11 ∧ Rest [.r2, .r3] s u ∧ u.mem = s.mem :=
  wp_mov (op2_reg s .r11) fun u₁ v₁ => wp_dp (op2_reg _ _) fun u₂ v₂ => WP.block_nil
    ⟨by rw [v₂.other _ (by decide), v₁.gpr], by rw [v₂.gpr, dpVal, v₁.other _ (by decide), v₁.other _ (by decide)],
      (v₁.rest (by decide)).trans (v₂.rest (by decide)), by rw [v₂.mem, v₁.mem]⟩

/-- The bytes' address and length, then the arguments. -/
theorem rhead_ok {s : State} (n : Nat) :
    WP isa (.block (([.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11)] : List Instr) ++ head n)) s fun u =>
      u.gpr .r2 = s.gpr .r11 ∧ u.gpr .r3 = s.gpr .lr - s.gpr .r11 ∧ u.gpr .r11 = s.gpr .r12 ∧
        u.gpr .r0 = s.gpr .r12 ∧ u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32 ∧
        Rest [.r0, .r1, .r2, .r3, .r11] s u ∧ u.mem = s.mem :=
  VG.Proof.X25519.Arm.WP.append rpre_ok fun u ⟨h2, h3, R, M⟩ => WP.mono (head_ok n) fun t ⟨h11, h0, h1, R', M'⟩ =>
    ⟨by rw [R'.gpr _ (by decide), h2], by rw [R'.gpr _ (by decide), h3],
      by rw [h11, R.gpr _ (by decide)], by rw [h0, R.gpr _ (by decide)], h1,
      (R.mono (by decide)).trans (R'.mono (by decide)), M'.trans M⟩

/-- On entry to the function, its precondition, narrowed to the context and
the bytes. -/
theorem rentry_pre {s u : State} {base : Addr} {size n len : Nat} {p : BitVec 32} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn48 : n ≤ 48) (h0 : u.gpr .r0 = s.gpr .r12)
    (h1 : u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32) (h2 : u.gpr .r2 = p)
    (h3 : (u.gpr .r3).toNat = len) (hfit : p.toNat + len ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩)
    (hm : u.mem = s.mem) (hodd : val32 s.mem base (slot n 0) (2 * n) % 2 = 1)
    (hm255 : 255 < val32 s.mem base (slot n 0) (2 * n)) :
    (reduceK n).pre (u.callEntry.withRegions [⟨State.addr p, len⟩] [⟨base, contextBytes n⟩]) := by
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by
    rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have l1 : (u.callEntry.gpr .r1).toNat * 8 = contextBytes n := by
    rw [State.callEntry_gpr _ (by decide), h1]; exact words_eq hn48
  have e2 : u.callEntry.gpr .r2 = p := by rw [State.callEntry_gpr _ (by decide), h2]
  have e3 : (u.callEntry.gpr .r3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3]
  simp only [reduceK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, b0, l1, e2, e3, hm]
  refine ⟨trivial, trivial, ?_, hfit, Nat.le_refl _, hd.symm, hodd, hm255⟩
  rw [State.callEntry_gpr _ (by decide), h0, hs.wb_toNat]
  have := hs.nowrap
  omega_using [hz, this]

theorem reduceCall_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (hv : val32 s.mem base (slot n 0) (2 * n) = m)
    (hm : 255 < m) (hodd : m % 2 = 1) (h11 : s.gpr .r11 = p) (hlr : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hfit : p.toNat + len ≤ 2 ^ 32) (llt : len < 2 ^ 32) (hr : InRegions (s.rd ++ s.wr) (State.addr p) len)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    WP isa (reduceCall n) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  have l3 : (s.gpr .lr - s.gpr .r11).toNat = len := by
    rw [hlr, h11, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt llt]
  unfold reduceCall
  refine WP.seq (WP.mono (rhead_ok n) fun u ⟨h2, h3, h11', h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := reduceK n) (reduceK_correct hn hn48)
    (rentry_pre hs hz hn48 h0 h1 (h2.trans h11) (by rw [h3, l3]) hfit hd M₁ (by rw [hv]; exact hodd)
      (by rw [hv]; exact hm))
    (Covers.append_left (Covers.one (by rw [R₁.rd, R₁.wr]; exact hr)) (Covers.right (covers_ctx w₁ hz)))
    (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (reduceBody_noFrames n))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have e2 : u.callEntry.gpr .r2 = p := by rw [State.callEntry_gpr _ (by decide), h2, h11]
  have e3 : (u.callEntry.gpr .r3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3, l3]
  simp only [reduceK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, e2, e3, M₁, hv]
    at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11']
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r2, .r3, .r11] := by
        revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

theorem reduceCall_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n len : Nat} {p : BitVec 32}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁)
    (hz₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 255 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 255 < val32 s₂.mem base (slot n 0) (2 * n))
    (a₁ : s₁.gpr .r11 = p) (l₁ : s₁.gpr .lr = p + BitVec.ofNat 32 len)
    (a₂ : s₂.gpr .r11 = p) (l₂ : s₂.gpr .lr = p + BitVec.ofNat 32 len)
    (hfit : p.toNat + len ≤ 2 ^ 32) (llt : len < 2 ^ 32) (hr₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr p) len)
    (hr₂ : InRegions (s₂.rd ++ s₂.wr) (State.addr p) len)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    SameTrace isa (reduceCall n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  have l3 : ∀ {s : State}, s.gpr .r11 = p → s.gpr .lr = p + BitVec.ofNat 32 len →
      (s.gpr .lr - s.gpr .r11).toNat = len := fun h11 hlr => by
    rw [hlr, h11, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt llt]
  unfold reduceCall head
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs [])
      (c₀ := .block [.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11), .mov .r11 (.reg .r12),
        .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (rhead_ok n) (rhead_ok n)
    fun u₁ u₂ ⟨h2₁, h3₁, _, h0₁, h1₁, R₁, M₁⟩ ⟨h2₂, h3₂, _, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (reduceK_correct hn hn48) (reduceK_ct n hn hn48) [⟨State.addr p, len⟩]
      [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨rentry_pre hs₁ hz₁ hn48 h0₁ h1₁ (h2₁.trans a₁) (by rw [h3₁, l3 a₁ l₁]) hfit hd M₁ ho₁ hm₁,
    rentry_pre hs₂ hz₂ hn48 h0₂ h1₂ (h2₂.trans a₂) (by rw [h3₂, l3 a₂ l₂]) hfit hd M₂ ho₂ hm₂, ?_,
    Covers.append_left (Covers.one (by rw [R₁.rd, R₁.wr]; exact hr₁)) (Covers.right (covers_ctx w₁ hz₁)),
    covers_ctx w₁ hz₁,
    Covers.append_left (Covers.one (by rw [R₂.rd, R₂.wr]; exact hr₂)) (Covers.right (covers_ctx w₂ hz₂)),
    covers_ctx w₂ hz₂⟩
  simp only [reduceK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    h0₁, h0₂, h2₁, h2₂, h3₁, h3₂, a₁, a₂, l₁, l₂]
  exact ⟨BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat]), rfl, rfl⟩

end VG.Proof.Dsa.Arm.Pow
