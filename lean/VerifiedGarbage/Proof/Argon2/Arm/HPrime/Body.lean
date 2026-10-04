import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Hash
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Argon2 H′ on ARMv7: the state of the body

`Body s₀ s`: between H′'s setup and its restore, `r4` points to `scratch`,
`r5` and `r6` hold the input and its length, the stack pointer is as on entry,
memory has changed only in the output, `scratch` and the stack below the
stack pointer, and the caller's registers and the length prefix are kept in
`scratch`. `Out s₀ s xs`: the output so far, `xs`, its pointer (`r7`) and the
bytes left (`r8`). `copy_ok`: copying digest bytes to the output.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (copy copyLoop saved baseSlot pfxOff)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_sub wp_subs wp_ldrb wp_strb op2_reg op2_imm sub_ofNat
  ofNat_beq_zero eval_ne eval_eq)
open VG.WriteBytes

/-- Where the caller's registers are, `r4` first. -/
abbrev saveList : List (Reg × Nat) := (.r4, baseSlot) :: saved

theorem saveList_slots : Spill.Slots 840 876 saveList := by decide

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

/-- The state of the body. -/
structure Body (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = scr s₀
  r5 : s.gpr .r5 = inp s₀
  r6 : s.gpr .r6 = s₀.gpr .r1
  sp : s.sp = sp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀, scrR s₀, stk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (P s₀) s₀.gpr saveList
  pfx : bytesAt s.mem (P s₀ + 832) 4 = Spec.Argon2.le32 (ol s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem Body.ctx {s : State} (h : Body s₀ s) : Ctx (scr s₀) (sp₀ s₀) s :=
  ⟨h.r4, h.sp, by have := hp.scr_fits; omega, hp.sp_lo,
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩),
    hp.stk_scr.sub_right (Region.sub_prefix (by decide))⟩

/-- A word of `scratch` from offset 832 on is kept by the hash macros. -/
theorem keeps_word {s t : State} (k : Keeps (scr s₀) (sp₀ s₀) s t) {d : Nat} (hd : 832 ≤ d)
    (hd' : d + 4 ≤ 16384) : t.mem.readW (P s₀ + BitVec.ofNat 64 d) 32 = s.mem.readW (P s₀ + BitVec.ofNat 64 d) 32 := by
  refine k.frame.readW (r := ⟨P s₀ + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ hd (by omega)
  · exact (hp.stk_scr.sub_right (Offset.sub_base _ (show d + 4 ≤ 16384 from hd'))).symm

theorem Body.keeps {s t : State} (h : Body s₀ s) (k : Keeps (scr s₀) (sp₀ s₀) s t) : Body s₀ t := by
  refine ⟨(k.gpr _ (by decide)).trans h.r4, (k.gpr _ (by decide)).trans h.r5, (k.gpr _ (by decide)).trans h.r6,
    k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (k.frame.sub fun r hr => ?_), fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stk s₀, by simp, fun _ h => h⟩
  · have hb := saveList_slots.bound hq
    rw [keeps_word hp k (by omega) (by omega)]; exact h.saved q hq
  · rw [← h.pfx]
    exact k.bytes (R := ⟨P s₀ + 832, 4⟩) (by simp) (Offset.disjoint_base _ (by decide) (by decide))
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))).symm

omit hp in
/-- A register write that keeps `r4`–`r6`. -/
theorem Body.upd {s t : State} (h : Body s₀ s) {d : Reg} {v : BitVec 32} (u : MdStream.Arm.Upd s t d v)
    (h4 : d ≠ .r4) (h5 : d ≠ .r5) (h6 : d ≠ .r6) : Body s₀ t :=
  ⟨by rw [u.other _ (Ne.symm h4), h.r4], by rw [u.other _ (Ne.symm h5), h.r5], by rw [u.other _ (Ne.symm h6), h.r6],
    by rw [u.sp, h.sp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.frame,
    by rw [u.mem]; exact h.saved, by rw [u.mem]; exact h.pfx⟩

end

/-! ## The output -/

/-- The output so far. -/
structure Out (s₀ s : State) (xs : List Byte) : Prop where
  ptr : s.gpr .r7 = op s₀ + BitVec.ofNat 32 xs.length
  left : s.gpr .r8 = BitVec.ofNat 32 (ol s₀ - xs.length)
  bytes : bytesAt s.mem (State.addr (op s₀)) xs.length = xs
  len : xs.length ≤ ol s₀

/-- The digest. -/
abbrev digest (s₀ s : State) : List Byte := bytesAt s.mem (P s₀ + 768) 64

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- The output is kept by the hash macros. -/
theorem Out.keeps {s t : State} {xs : List Byte} (h : Out s₀ s xs)
    (k : Keeps (scr s₀) (sp₀ s₀) s t) : Out s₀ t xs := by
  refine ⟨(k.gpr _ (by decide)).trans h.ptr, (k.gpr _ (by decide)).trans h.left, ?_, h.len⟩
  have kb := k.bytes (R := ⟨State.addr (op s₀), xs.length⟩)
    (by have := h.len; have := hp.out_fits; simp; omega)
    ((hp.out_scr.sub_left (Region.sub_prefix h.len)).sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_out.sub_right (Region.sub_prefix h.len)).symm)
  simp only at kb
  rw [kb]; exact h.bytes

/-! ## Copying digest bytes -/

/-- The copy loop's state after `j` of `n` bytes, from `s`: the bytes go from
the digest to `op + k`. -/
structure CopyI (s₀ s : State) (k n j : Nat) (t : State) : Prop where
  j_le : j ≤ n
  r9 : t.gpr .r9 = scr s₀ + 768 + BitVec.ofNat 32 j
  r7 : t.gpr .r7 = op s₀ + BitVec.ofNat 32 (k + j)
  r10 : t.gpr .r10 = BitVec.ofNat 32 (n - j)
  other : ∀ x, x ≠ .r12 → x ≠ .r9 → x ≠ .r7 → x ≠ .r10 → t.gpr x = s.gpr x
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (State.addr (op s₀) + BitVec.ofNat 64 k) ((digest s₀ s).take j)

omit hp in
theorem setWidth_byte (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

theorem copyLoop_ok {s : State} (b : Body s₀ s) {k n : Nat} (hk : s.gpr .r7 = op s₀ + BitVec.ofNat 32 k)
    (h9 : s.gpr .r9 = scr s₀ + 768) (hn : s.gpr .r10 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64)
    (hkn : k + n ≤ ol s₀) {Q : State → Prop} (hQ : ∀ t, CopyI s₀ s k n n t → Q t) :
    WP isa copyLoop s Q := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  have dgR : Region.Disjoint ⟨P s₀ + 768, 64⟩ ⟨State.addr (op s₀) + BitVec.ofNat 64 k, n⟩ :=
    ((hp.out_scr.sub_left (Offset.sub_base _ (d := k) (n := n) (k := ol s₀) (by omega))).sub_right
      (Offset.sub_base (P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
  refine WP.loop (M := isa) (fun m (t : State) => ∃ j, m = n - j ∧ j < n ∧ CopyI s₀ s k n j t) ?_ n s
    ⟨0, by omega, by omega, ⟨by omega, by simp [h9], by simp [hk], by rw [hn, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩⟩
  rintro m t ⟨j, rfl, hj, h⟩
  have e768 : State.addr (scr s₀ + 768) = P s₀ + 768 := addr_add (k := 768) (by omega)
  -- The byte read.
  have hin : InRegions (t.rd ++ t.wr) (P s₀ + 768 + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr, b.rd, b.wr, hp.wr]
    refine ⟨scrR s₀, by simp, ?_⟩
    rw [show P s₀ + 768 + BitVec.ofNat 64 j = P s₀ + BitVec.ofNat 64 (768 + j) from Offset.add_add _ 768 j]
    exact Offset.contains_base _ (by omega) (by omega)
  have hbyte : t.mem (P s₀ + 768 + BitVec.ofNat 64 j) = s.mem (P s₀ + 768 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hl : ((digest s₀ s).take j).length ≤ n := by simp [digest, bytesAt]; omega
    exact (writeBytes_frame (R := ⟨State.addr (op s₀) + BitVec.ofNat 64 k, n⟩) s.mem _ _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hl)).bytes
      (R := ⟨P s₀ + 768, 64⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dgR)
      (by show (64 : Nat) ≤ 2 ^ 64; decide) (show j < 64 by omega)
  -- The byte written.
  have hout : InRegions t.wr (State.addr (op s₀) + BitVec.ofNat 64 (k + j)) 1 := by
    rw [h.wr, b.wr, hp.wr]
    exact ⟨outR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ldrb (a := P s₀ + 768 + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r9, BitVec.add_zero, addr_add (by rw [BitVec.toNat_add]; simp; omega), e768]) hin
    fun s₁ u₁ => ?_
  refine wp_strb (a := State.addr (op s₀) + BitVec.ofNat 64 (k + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.r7, BitVec.add_zero, addr_add (by omega)])
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  have hr10 : s₅.gpr .r10 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r10,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hI : CopyI s₀ s k n (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hr10, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r9,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r7,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₅.other x h4, u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3 h4]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (digest s₀ s).length := by simp [digest, bytesAt]; omega
      have hl : (List.take j (digest s₀ s)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte, Offset.add_add]
      congr 1
      simp [digest, bytesAt]
  have hz : isa.eval .ne s₅ = some (decide (n - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s₅ = _
    rw [eval_ne, z₅, ← u₅.gpr, hr10, ofNat_beq_zero (by omega)]
    simp
  by_cases hjn : j + 1 = n
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjn ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, n - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-- Emit `n` digest bytes after the output `xs`. -/
theorem copyOut_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs) {n : Nat}
    (hn : s.gpr .r10 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : xs.length + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (op s₀)) (xs.length + n) = xs ++ (digest s₀ s).take n ∧
      t.gpr .r7 = op s₀ + BitVec.ofNat 32 (xs.length + n) ∧ digest s₀ t = digest s₀ s := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  unfold copy
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : Body s₀ s₁ := b.keeps hp (Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr)
  refine copyLoop_ok hp b₁ (k := xs.length) (n := n) (by rw [u₁.other _ (by decide), h.ptr])
    (by rw [u₁.gpr, b.r4]) (by rw [u₁.other _ (by decide), hn]) hn₁ hn₂ hkn fun t ht => ?_
  have dgR : Region.Disjoint ⟨P s₀ + 768, 64⟩ ⟨State.addr (op s₀) + BitVec.ofNat 64 xs.length, n⟩ :=
    ((hp.out_scr.sub_left (Offset.sub_base _ (d := xs.length) (n := n) (k := ol s₀) (by omega))).sub_right
      (Offset.sub_base (P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
  have lenL : ((digest s₀ s₁).take n).length = n := by simp [digest, bytesAt]; omega
  have F : Frame [⟨State.addr (op s₀) + BitVec.ofNat 64 xs.length, n⟩] s₁.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [lenL]; exact Region.contains_self _ _)
  have outSub : Region.Sub ⟨State.addr (op s₀) + BitVec.ofNat 64 xs.length, n⟩ (outR s₀) :=
    Offset.sub_base _ (by omega)
  have d₁ : digest s₀ s₁ = digest s₀ s := by simp only [digest, u₁.mem]
  have dt : digest s₀ t = digest s₀ s₁ :=
    Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨P s₀ + 768, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dgR) (by simp) hi
  refine ⟨⟨by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r4],
      by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r5],
      by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r6],
      by rw [ht.sp, b₁.sp], by rw [ht.rd, b₁.rd], by rw [ht.wr, b₁.wr],
      b₁.frame.trans (F.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨outR s₀, by simp, outSub⟩),
      fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, dt.trans d₁⟩
  · have hb := saveList_slots.bound hq
    rw [F.readW (r := ⟨P s₀ + BitVec.ofNat 64 q.2, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ (by omega))).symm) (by decide)]
    exact b₁.saved q hq
  · rw [← b₁.pfx]
    exact Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨P s₀ + 832, 4⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ (by decide))).symm) (by simp) hi
  · rw [ht.other _ (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide)]
  · rw [ht.other _ (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide)]
  · have old : bytesAt t.mem (State.addr (op s₀)) xs.length = bytesAt s₁.mem (State.addr (op s₀)) xs.length :=
      Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨State.addr (op s₀), xs.length⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)) (by have := h.len; simp; omega) hi
    have new : bytesAt t.mem (State.addr (op s₀) + BitVec.ofNat 64 xs.length) n = (digest s₀ s₁).take n := by
      rw [ht.mem]
      have := bytesAt_writeBytes s₁.mem (State.addr (op s₀) + BitVec.ofNat 64 xs.length)
        ((digest s₀ s₁).take n) (by rw [lenL]; omega)
      rwa [lenL] at this
    rw [Proof.Blake2.bytesAt_add, new, old, d₁, u₁.mem, h.bytes]
  · exact ht.r7

/-- Emit a 32-byte prefix of the digest. -/
theorem emit_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hkn : xs.length + 32 ≤ ol s₀) :
    WP isa Impl.Argon2.Arm.HPrime.emitPrefix s fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      Out s₀ t (xs ++ (digest s₀ s).take 32) ∧ digest s₀ t = digest s₀ s := by
  unfold Impl.Argon2.Arm.HPrime.emitPrefix
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : Keeps (scr s₀) (sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  refine WP.seq ((copyOut_ok hp (b.keeps hp k₁) (h.keeps hp k₁) u₁.gpr (by decide) (by decide) hkn).mono
    fun s₂ ⟨b₂, l₂, e₂, by₂, p₂, d₂⟩ => ?_)
  refine wp_sub (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have len' : (xs ++ (digest s₀ s).take 32).length = xs.length + 32 := by
    simp [digest, bytesAt]
  refine ⟨b₂.upd u₃ (by decide) (by decide) (by decide), by rw [u₃.other _ (by decide), e₂, u₁.other _ (by decide)],
    ⟨?_, ?_, ?_, by rw [len']; exact hkn⟩, by simp only [digest, u₃.mem]; exact d₂.trans (by simp only [digest, u₁.mem])⟩
  · rw [len', u₃.other _ (by decide), p₂]
  · rw [len', u₃.gpr, l₂, u₁.other _ (by decide), h.left]
    exact (sub_ofNat (a := ol s₀ - xs.length) (b := 32) (by omega)).trans (by congr 1)
  · rw [len', u₃.mem, by₂, show digest s₀ s₁ = digest s₀ s by simp only [digest, u₁.mem]]

/-- Copy the bytes left. -/
theorem copyRemaining_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hn₁ : xs.length < ol s₀) (hn₂ : ol s₀ - xs.length ≤ 64) :
    WP isa Impl.Argon2.Arm.HPrime.copyRemaining s fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (op s₀)) (ol s₀) = xs ++ (digest s₀ s).take (ol s₀ - xs.length) := by
  unfold Impl.Argon2.Arm.HPrime.copyRemaining
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : Keeps (scr s₀) (sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  refine (copyOut_ok hp (b.keeps hp k₁) (h.keeps hp k₁) (n := ol s₀ - xs.length)
    (by rw [u₁.gpr, h.left]) (by omega) hn₂ (by omega)).mono
    fun t ⟨bt, _, et, byt, _, _⟩ => ⟨bt, by rw [et, u₁.other _ (by decide)], ?_⟩
  rw [show xs.length + (ol s₀ - xs.length) = ol s₀ by omega] at byt
  rw [byt]; simp only [digest, u₁.mem]

end

end VG.Proof.Argon2.Arm.HPrime
