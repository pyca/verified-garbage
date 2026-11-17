module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem
public import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.X448.X86.Counters
public import VerifiedGarbage.Proof.X448.Ladder
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.ByteMem
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.Framework.Range

/-! ### `X448.X86.BitWrite`, which this module and modules that import it used -/

section

/-!
# X448 on x86 (32-bit): expanding a scalar byte

Public shifts select each bit and write it to its own byte in the working
space, through `ebp`, which `bitsLoop` keeps at `edi + 8 i` for byte `i`.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem bitShift_ok {s : State} {j : Nat} (hj : j < 8) :
    WP isa (.block (([.mov .edx (.reg .eax)] : List Instr) ++
      if j = 0 then [] else [.shift .shr .edx j])) s fun t =>
      t.gpr .edx = s.gpr .eax >>> j ∧ t.mem = s.mem ∧ Keeps [.edx] s t := by
  refine wp_mov rfl fun t ht => ?_
  by_cases hz : j = 0
  · subst j
    exact WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩
  · rw [ite_eq_right hz]
    refine wp_shift (by omega_using [hj, hz]) fun u hu => WP.block_nil ⟨?_, hu.mem.trans ht.mem,
      (ht.rest (by decide)).trans (hu.rest (by decide))⟩
    rw [hu.gpr, ht.gpr]

/-- Bit `j` of the byte `b` in `eax` to byte `d + (o + j)` of the working space, for
`ebp = edi + d`. -/
theorem bitP_ok {s : State} {base : Addr} (hs : Scr s base) {o d : Nat} (hd : d + o + 8 ≤ 8192)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 d)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitP o j)) s fun t =>
      t.mem = s.mem.writeW (off base (d + (o + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
        Keeps [.edx] s t := by
  rw [bitP, WP.block_append_iff]
  refine WP.mono (bitShift_ok hj) fun t ⟨tv, tm, tk⟩ => ?_
  refine wp_alu (by simp [plain]) rfl fun u hu _ => ?_
  have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 d := by
    rw [hu.other _ (by decide), hu.other _ (by decide), tk.1 _ (by decide), tk.1 _ (by decide), hp]
  refine wp_store8 (us.ea_ptr up (by omega_using [hd, hj])) (us.write (d := d + (o + j)) (n := 1) (by omega_using [hd, hj]))
    fun v hv => WP.block_nil ⟨?_, tk.trans ?_⟩
  · rw [hv.mem, hu.mem, tm, Reg8.reg, hu.gpr]
    change s.mem.writeW _ ((t.gpr .edx &&& (1 : BitVec 32)).setWidth 8) = _
    rw [tv, ha, bit_byte b j hj]
  · exact (hu.rest (by decide)).trans (hv.rest _)

/-- The eight bits of the byte `b` in `eax` to bytes `d + o`, …, `d + o + 7`, for `ebp = edi + d`. -/
theorem byteP_ok {s : State} {base : Addr} (hs : Scr s base) {o d : Nat} (hd : d + o + 8 ≤ 8192)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 d)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (bitP o))) s fun t =>
      (∀ j < 8, t.mem (off base (d + (o + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (d + o) 8 s.mem t.mem ∧ Keeps [.edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (d + (o + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (d + o) 8 s.mem t.mem ∧ Keeps [.edx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitP o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (bitP_ok (hs.of_keeps tk (by decide)) hd
      ((tk.1 _ (by decide)).trans (hp.trans (by rw [tk.1 _ (by decide)])))
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (d + (o + j)) = off base (d + (o + n)) ↔ j = n := by
        rw [off_eq_iff base (by omega_using [hd, hn, hj]) (by omega_using [hd, hn])]
        omega_using []
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega_using [hj, he])
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by omega_using [hd, hn]) (by omega_using [hn, hx])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.Clamp`, which only this module used -/

section

/-!
# X448 on x86 (32-bit): clamping the scalar bits

Clear bits zero and one, and set bit 447, as RFC 7748 requires.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (off base BITS) (0 : BitVec 8)).writeW (off base (BITS + 1))
    (0 : BitVec 8)).writeW (off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.store8 (sc d) .dl]) s fun t =>
      t.mem = s.mem.writeW (off base d) ((s.gpr .edx).setWidth 8) ∧ Keeps [] s t := by
  refine wp_store8 (hs.ea (d := d) (by omega_using [hd])) (hs.write (d := d) (n := 1) (by omega_using [hd]))
    fun t ht => WP.block_nil ⟨ht.mem, (ht.rest _)⟩

theorem putByte_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 32) :
    WP isa (.block [.mov .edx (.imm v), .store8 (sc d) .dl]) s fun t =>
      t.mem = s.mem.writeW (off base d) (v.setWidth 8) ∧
      t.gpr .edx = v ∧ Keeps [.edx] s t := by
  refine wp_mov rfl fun t ht => ?_
  refine WP.mono (storeByte_ok (hs.of_upd ht (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  exact ⟨by rw [um, ht.mem, ht.gpr], (uk.1 _ (by decide)).trans ht.gpr,
    ((ht.rest (by decide))).trans (uk.mono (by simp))⟩

theorem clamp_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clamp) s fun t => t.mem = clampMem s.mem base ∧ Keeps [.edx] s t := by
  change WP isa (.block (([.mov .edx (.imm 0), .store8 (sc BITS) .dl] : List Instr) ++
    ([.store8 (sc (BITS + 1)) .dl] : List Instr) ++
    [.mov .edx (.imm 1), .store8 (sc (BITS + 447)) .dl])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (putByte_ok hs (by decide : BITS < 4096) 0) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): decoding the scalar bits

`bitsLoop o n` expands the `n` bytes at `esi` into their bits at `o`, one byte
per iteration (`bitsLoop_ok`); X448 expands 56 bytes and then clears bits zero
and one and sets bit 447 (`bitsData_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

def bitRegs : List Reg := [.eax, .edx, .ecx, .ebp, .esi]

/-- The end of an iteration: `esi`, `ebp` and the count `ecx` moved on. -/
theorem bitsTail_ok {s : State} {m : Nat} (hm : m < 2 ^ 16) (hc : s.gpr .ecx = BitVec.ofNat 32 (m + 1)) :
    WP isa (.block [.alu .add .esi (.imm 1), .alu .add .ebp (.imm 8), .alu .sub .ecx (.imm 1)]) s
      fun t => t.gpr .esi = s.gpr .esi + BitVec.ofNat 32 1 ∧ t.gpr .ebp = s.gpr .ebp + BitVec.ofNat 32 8 ∧
        t.gpr .ecx = BitVec.ofNat 32 m ∧ t.zf = some (decide (m = 0)) ∧ t.mem = s.mem ∧
        Keeps [.esi, .ebp, .ecx] s t := by
  refine wp_alu (Or.inl rfl) rfl fun t ht _ => ?_
  refine wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  have he : u.gpr .ecx - (1 : BitVec 32) = BitVec.ofNat 32 m := by
    change u.gpr .ecx - BitVec.ofNat 32 1 = _
    rw [hu.other _ (by decide), ht.other _ (by decide), hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun v hv hz => WP.block_nil ⟨?_, ?_, hv.gpr.trans he, ?_,
    hv.mem.trans (hu.mem.trans ht.mem), (ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      (hv.rest (by decide)))⟩
  · rw [hv.other _ (by decide), hu.other _ (by decide), ht.gpr]; rfl
  · rw [hv.other _ (by decide), hu.gpr, ht.other _ (by decide)]; rfl
  · rw [hz]
    change some (u.gpr .ecx - (1 : BitVec 32) == 0) = _
    rw [he, ofNat_beq_zero (by omega_arith)]

/-- One iteration, for byte `i` (`m + 1` left): its bits to bytes `o + 8 i + j`. -/
theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) {o n i m : Nat} (hin : i + m + 1 = n)
    (hn : n ≤ 64) (ho : o + 8 * n ≤ 8192) {p : BitVec 32} (hk : p.setWidth 64 = k)
    (hfit : p.toNat + n ≤ 2 ^ 32) (hsi : s.gpr .esi = p + BitVec.ofNat 32 i)
    (hbp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (8 * i)) (hcx : s.gpr .ecx = BitVec.ofNat 32 (m + 1))
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block (bitsBody o)) s fun t =>
      t.gpr .esi = p + BitVec.ofNat 32 (i + 1) ∧
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (8 * (i + 1)) ∧
      t.gpr .ecx = BitVec.ofNat 32 m ∧ t.zf = some (decide (m = 0)) ∧ Keeps bitRegs s t ∧
      (∀ j < 8, t.mem (off base (o + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (8 * i + o) 8 s.mem t.mem := by
  have ea : s.ea (at_ .esi 0) = off k i := by
    change addr (s.gpr .esi) 0 = _
    rw [hsi, show addr (p + BitVec.ofNat 32 i) 0 = addr p i by simp only [addr, BitVec.add_zero],
      addr_eq (by omega_arith), hk]
  change WP isa (.block (.movzx8 .eax (at_ .esi 0) :: ((List.range 8).flatMap (bitP o) ++
    [.alu .add .esi (.imm 1), .alu .add .ebp (.imm 8), .alu .sub .ecx (.imm 1)]))) s _
  refine wp_load8 ea hr fun t ht => ?_
  rw [WP.block_append_iff]
  have ts := hs.of_upd ht (by decide)
  refine WP.mono (byteP_ok ts (o := o) (d := 8 * i) (by omega_arith)
    (by rw [ht.other _ (by decide), ht.other _ (by decide), hbp]) ht.gpr) fun u ⟨ub, um, uk⟩ => ?_
  have uc : u.gpr .ecx = BitVec.ofNat 32 (m + 1) :=
    (uk.1 _ (by decide)).trans ((ht.other _ (by decide)).trans hcx)
  refine WP.mono (bitsTail_ok (by omega_arith) uc) fun v ⟨vs, vp, vc, vz, vm, vk⟩ => ?_
  have ue : u.gpr .edi = s.gpr .edi := (uk.1 _ (by decide)).trans (ht.other _ (by decide))
  refine ⟨?_, ?_, vc, vz, ?_, fun j hj => ?_, ?_⟩
  · rw [vs, uk.1 _ (by decide), ht.other _ (by decide), hsi, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [vp, vk.1 _ (by decide), uk.1 _ (by decide), ht.other _ (by decide), ue, hbp, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 8 * i + 8 = 8 * (i + 1) by omega_arith]
  · refine (ht.rest (by decide)).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide
  · rw [vm, show o + (8 * i + j) = 8 * i + (o + j) by omega_arith, ub j hj]
  · rw [vm, ← ht.mem]; exact um

/-- `bitsLoop o n`: the `n` bytes at `esi` expanded into their bits, byte `o + j` of the working
space bit `j % 8` of byte `j / 8`. -/
theorem bitsLoop_ok {s : State} {base k : Addr} (hs : Scr s base) {o n : Nat} (hn1 : 1 ≤ n)
    (hn : n ≤ 64) (ho : o + 8 * n ≤ 8192)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + n ≤ 2 ^ 32)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < n, 8192 ≤ ofs base (off k i)) :
    WP isa (bitsLoop o n) s fun t =>
      Keeps bitRegs s t ∧ Outside base o (8 * n) s.mem t.mem ∧
      (∀ j < 8 * n, t.mem (off base (o + j)) =
        BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1)) ∧
      t.gpr .esi = s.gpr .esi + BitVec.ofNat 32 n := by
  let p := s.gpr .esi
  let Q := fun (t : State) => Keeps bitRegs s t ∧ Outside base o (8 * n) s.mem t.mem ∧
    (∀ j < 8 * n, t.mem (off base (o + j)) =
      BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1)) ∧
    t.gpr .esi = p + BitVec.ofNat 32 n
  let inv := fun m (t : State) => 1 ≤ m ∧ m ≤ n ∧ Keeps bitRegs s t ∧
    t.gpr .esi = p + BitVec.ofNat 32 (n - m) ∧ t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (8 * (n - m)) ∧
    t.gpr .ecx = BitVec.ofNat 32 m ∧ Outside base o (8 * n) s.mem t.mem ∧
    ∀ j < 8 * (n - m), t.mem (off base (o + j)) =
      BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1)
  unfold bitsLoop
  refine WP.seq (wp_mov rfl fun t ht => wp_mov rfl fun u hu => WP.block_nil ?_)
  refine WP.loop (M := isa) (Q := Q) inv ?_ n u ⟨hn1, Nat.le_refl _, ?_, ?_, ?_, hu.gpr, ?_, fun j hj => by omega_arith⟩
  · intro m v ⟨hm1, hmn, vk, vs, vp, vc, vo, vb⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
    have vS := hs.of_keeps vk (by decide)
    refine WP.mono (bitsBody_ok vS (o := o) (n := n) (i := n - (m + 1)) (m := m) (by omega_arith) hn ho
      (p := p) hk hfit vs vp vc (by rw [vk.2.1, vk.2.2]; exact hr _ (by omega_arith)))
      fun w ⟨ws, wp, wc, wz, wk, wb, wo⟩ => ?_
    have src : v.mem (off k (n - (m + 1))) = s.mem (off k (n - (m + 1))) :=
      vo _ (Or.inr (by have := hd (n - (m + 1)) (by omega_arith); omega_arith))
    have wo' : Outside base o (8 * n) s.mem w.mem :=
      vo.trans (wo.mono (by omega_arith) (by omega_arith))
    have wb' : ∀ j < 8 * (n - m), w.mem (off base (o + j)) =
        BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1) := by
      intro j hj
      rcases Nat.lt_or_ge j (8 * (n - (m + 1))) with h | h
      · rw [wo _ (Or.inl (by rw [ofs_off' base (by omega_arith)]; omega_arith))]
        exact vb j h
      · have e := wb (j - 8 * (n - (m + 1))) (by omega_arith)
        rw [show 8 * (n - (m + 1)) + (j - 8 * (n - (m + 1))) = j by omega_arith, src] at e
        rw [e, show j / 8 = n - (m + 1) by omega_arith, show j % 8 = j - 8 * (n - (m + 1)) by omega_arith]
    simp only [eval, wz, Option.map_some]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine .inl ⟨rfl, vk.trans wk, wo', fun j hj => wb' j (by omega_arith), by
        rw [ws, show n - (0 + 1) + 1 = n by omega_arith]⟩
    · refine .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
        by omega_arith, by omega_arith, vk.trans wk, ?_, ?_, wc, wo', wb'⟩
      · rw [ws, show n - (m + 1) + 1 = n - m by omega_arith]
      · rw [wp, show n - (m + 1) + 1 = n - m by omega_arith]
  · refine (ht.rest (by simp [bitRegs])).trans (hu.rest (by simp [bitRegs]))
  · rw [hu.other _ (by decide), ht.other _ (by decide), Nat.sub_self]; exact (BitVec.add_zero _).symm
  · rw [hu.other _ (by decide), ht.gpr, hu.other _ (by decide), ht.other _ (by decide), Nat.sub_self,
      Nat.mul_zero]
    exact (BitVec.add_zero _).symm
  · rw [hu.mem, ht.mem]; exact Outside.refl _ _ _ _

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- Expanded and clamped bytes are precisely the decoded scalar's bits. -/
theorem bitsData_ok {s : State} {base k : Addr} (hs : Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ i < 56, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < 56, 8192 ≤ ofs base (off k i)) :
    WP isa (.seq (bitsLoop BITS 56) (.block clamp)) s fun t =>
      Keeps bitRegs s t ∧ Outside base BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) j) := by
  refine WP.seq (WP.mono (bitsLoop_ok hs (by decide) (by decide) (by decide) hk hfit hr hd)
    fun s₂ ⟨k₂, o₂, b₂, _⟩ => ?_)
  refine WP.mono (clamp_ok (hs.of_keeps k₂ (by decide))) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine ⟨k₂.trans (k₃.mono (by simp [bitRegs])), fun x hx => ?_, fun t ht => ?_⟩
  · rw [m₃, clampMem]
    have o : ∀ d, BITS ≤ d → d < BITS + 448 → ofs base x ≠ d := fun d h₁ h₂ h => by omega_arith
    rw [writeW8_outside _ _ _ (by simp only [BITS]; omega_arith) (o (BITS + 447) (by omega_arith) (by omega_arith)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega_arith) (o (BITS + 1) (by omega_arith) (by omega_arith)),
      writeW8_outside _ _ _ (by simp only [BITS]; omega_arith) (o BITS (by omega_arith) (by omega_arith))]
    exact o₂ x hx
  · rw [m₃, clampMem, scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega_arith) only [writeW8_apply, off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega_arith : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega_arith, show t ≠ 1 by omega_arith, show t ≠ 0 by omega_arith,
        show ¬t < 2 by omega_arith, ite_false]
      rw [b₂ t (by omega_arith), getD_bytesAt _ _ (by omega_arith)]

end VG.Proof.X448.X86
