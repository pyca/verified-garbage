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

theorem stream_inside {n : Nat} : ∀ r ∈ streamRanges n, r.1 + r.2 ≤ contextBytes n := by
  simp only [streamRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    contextBytes, slot, stride]
  omega_arith

theorem words_inside {n : Nat} (hn48 : n ≤ 48) : ∀ r ∈ words slots, r.1 + r.2 ≤ contextBytes n :=
  fun r h => by have := slots_words r h; have := contextBytes_bounds hn48; omega_arith

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
