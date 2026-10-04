import VerifiedGarbage.Proof.Ed448.X86.ScalarStep
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.X448.X86.Fill

/-!
# Ed448 scalar arithmetic on x86 (32-bit): the loops

The remainder of an input's bytes from the top, sixteen bits at a time
(`byteLoop_ok`), and of the product's limbs (`limbLoop_ok`), and the
remainders they start from (`zeroR_ok`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR readBytes byteStep zeroR readLimb limbStep step)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `[x + n + d]`, for `x + n + d` below `2^32`. -/
theorem addr_add2 (x : BitVec 32) {n d : Nat} (h : x.toNat + n + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 n) d = x.setWidth 64 + BitVec.ofNat 64 (n + d) := by
  rw [← addr_eq (by omega)]
  simp only [addr, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## What the loops change -/

/-- What the loops leave unchanged: all registers but `eax`, `ebx`, `ecx`,
`edx` and `ebp`, and the memory outside `[W, TF + 112)` and the remainder at
`o`. -/
structure LoopKeep (base : Addr) (o : Nat) (s t : State) : Prop where
  regs : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t
  mem : Outside2 base W 160 o 112 s.mem t.mem

theorem LoopKeep.refl (base : Addr) (o : Nat) (s : State) : LoopKeep base o s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem LoopKeep.trans {base : Addr} {o : Nat} {s t u : State} (h : LoopKeep base o s t)
    (h' : LoopKeep base o t u) : LoopKeep base o s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

/-- A step's frame, and the chunk's store, within the loops'. -/
theorem outside2_step {base : Addr} {o : Nat} {m m' : Mem} (h : Outside2 base TF 112 o 112 m m') :
    Outside2 base W 160 o 112 m m' := fun p h1 h2 => h p (by simp only [TF, W] at h1 ⊢; omega) h2

theorem outside2_W {base : Addr} {o : Nat} {m m' : Mem} (h : Outside base W 4 m m') :
    Outside2 base W 160 o 112 m m' := fun p h1 _ => h p (by simp only [W] at h1 ⊢; omega)

/-- A byte beyond the working space, unchanged across the loops. -/
theorem outside2_byte {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : Outside2 base x nx y ny m m')
    {a : Addr} (ha : 8192 ≤ ofs base a) (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) : m' a = m a :=
  h a (Or.inr (by omega)) (Or.inr (by omega))

/-! ## Reading two bytes -/

theorem readBytes_ok {s : State} {base : Addr} (hs : Scr s base) {p : BitVec 32} {n N : Nat}
    (hn : n + 2 ≤ N) (hp : s.gpr .esi = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hc : s.gpr .ebp = BitVec.ofNat 32 (n + 2))
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1) :
    WP isa (.block readBytes) s fun t =>
      Keeps [.eax, .edx, .ebp] s t ∧ Outside base W 4 s.mem t.mem ∧ t.gpr .ebp = BitVec.ofNat 32 n ∧
      (word t.mem base W).toNat = (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).toNat +
        256 * (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).toNat := by
  unfold readBytes
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun s1 u1 _ => ?_
  refine wp_mov rfl fun s2 u2 => wp_alu (Or.inl rfl) rfl fun s3 u3 _ => ?_
  have e1 : s1.gpr .ebp = BitVec.ofNat 32 n := by
    rw [u1.gpr]
    change s.gpr .ebp - BitVec.ofNat 32 2 = _
    rw [hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e3 : s3.gpr .edx = p + BitVec.ofNat 32 n := by
    rw [u3.gpr]
    change s2.gpr .edx + s2.gpr .ebp = _
    rw [u2.gpr, u2.other .ebp (by decide), u1.other .esi (by decide), hp, e1]
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 n)
    (by change addr (s3.gpr .edx) 0 = _; rw [e3, addr_add2 p (by omega), Nat.add_zero])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr n (by omega)) fun s4 u4 => ?_
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 (n + 1))
    (by change addr (s4.gpr .edx) 1 = _; rw [u4.other .edx (by decide), e3, addr_add2 p (by omega)])
    (by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr (n + 1) (by omega))
    fun s5 u5 => ?_
  refine wp_shift (by decide) fun s6 u6 => wp_alu (Or.inl rfl) rfl fun s7 u7 _ => ?_
  have hs7 := ((((((hs.of_upd u1 (by decide)).of_upd u2 (by decide)).of_upd u3 (by decide)).of_upd u4
    (by decide)).of_upd u5 (by decide)).of_upd u6 (by decide)).of_upd u7 (by decide)
  refine store_ok hs7 (by simp only [W]; omega) fun s8 u8 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
        ((u7.rest (by decide)).trans (u8.rest _)))))))
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, m3]
    exact writeW_outside _ _ _ (by simp only [W]; omega)
  · rw [u8.gpr, u7.other .ebp (by decide), u6.other .ebp (by decide), u5.other .ebp (by decide),
      u4.other .ebp (by decide), u3.other .ebp (by decide), u2.other .ebp (by decide), e1]
  · have value : s7.gpr .eax = BitVec.ofNat 32 ((s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).toNat +
        256 * (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).toNat) := by
      rw [u7.gpr]
      change s6.gpr .eax + s6.gpr .edx = _
      have : s6.gpr .edx = (s5.gpr .edx).rotateRight 24 := u6.gpr
      rw [u6.other .eax (by decide), this, u5.other .eax (by decide), u4.gpr, u5.gpr, u4.mem, m3,
        byte_rotate]
      apply BitVec.eq_of_toNat_eq
      have h0 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).isLt
      have h1 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).isLt
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.shiftLeft_eq, BitVec.toNat_ofNat]
      omega
    have hw : (word s8.mem base W) = s7.gpr .eax := by
      rw [u8.mem, word, Mem.readW_writeW_self32]
    rw [hw, value]
    have h0 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).isLt
    have h1 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).isLt
    exact toNat_imm (by omega)

/-! ## The byte loop -/

/-- After the steps from the top down to byte `n`. -/
structure ByteInv (base : Addr) (o N : Nat) (P : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ N
  even : n % 2 = 0
  counter : s.gpr .ebp = BitVec.ofNat 32 n
  lim : Bounded s.mem base o
  value : fe s.mem base o = decodeLE ((bytesAt s0.mem P N).drop n) % L
  keeps : LoopKeep base o s0 s

theorem cmp_zero {s : State} {n : Nat} (hn : n < 2 ^ 32) (hc : s.gpr .ebp = BitVec.ofNat 32 n)
    {t : State} (hz : t.zf = some (s.gpr .ebp - 0 == 0)) : t.zf = some (decide (n = 0)) := by
  rw [hz, hc, show BitVec.ofNat 32 n - (0 : BitVec 32) = BitVec.ofNat 32 n from BitVec.sub_zero _,
    ofNat_beq_zero hn]

theorem byteLoop_ok {o N : Nat} (ho : Buf o) {s0 : State} {base : Addr} (hs : Scr s0 base)
    {p : BitVec 32} (hp : s0.gpr .esi = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hread : ∀ i < N, InRegions (s0.rd ++ s0.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hfar : ∀ i < N, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 i))
    {n0 : Nat} (hn0 : 0 < n0) (hle : n0 ≤ N) (heven : n0 % 2 = 0)
    (hc : s0.gpr .ebp = BitVec.ofNat 32 n0) (hl : Bounded s0.mem base o)
    (hv : fe s0.mem base o = decodeLE ((bytesAt s0.mem (p.setWidth 64) N).drop n0) % L) :
    WP isa (.loop (.block (byteStep o)) .ne) s0 fun t => LoopKeep base o s0 t ∧
      Bounded t.mem base o ∧ fe t.mem base o = decodeLE (bytesAt s0.mem (p.setWidth 64) N) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hN : N ≤ 2 ^ 32 := by omega
  apply WP.loop (ByteInv base o N (p.setWidth 64) s0) (n := n0)
  · intro n s hi
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := hi.even; have := hi.positive; omega⟩
    have hk : k + 2 ≤ N := hi.bound
    have hss : Scr s base := hs.of_keeps hi.keeps.regs (by decide)
    have hps : s.gpr .esi = p := (hi.keeps.regs.1 _ (by decide)).trans hp
    have hrs : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1 := by
      rw [hi.keeps.regs.2.1, hi.keeps.regs.2.2]; exact hread
    unfold byteStep
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (readBytes_ok hss hk hps hfit hi.counter hrs) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hsu : Scr u base := hss.of_keeps ku (by decide)
    have hwu : (word u.mem base W).toNat < radix := by
      rw [wu]
      have := (s.mem (p.setWidth 64 + BitVec.ofNat 64 k)).isLt
      have := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (k + 1))).isLt
      simp only [radix]
      omega
    have lu : ∀ j < 28, limbs u.mem base o j = limbs s.mem base o j :=
      fun j hj => mu.limbs (Or.inr (by simp only [W, TF] at ho1 ⊢; omega)) (by omega) hj
    have fu : fe u.mem base o = fe s.mem base o := valN_congr lu
    rw [WP.block_append_iff]
    refine WP.mono (step_ok ⟨ho1, ho2⟩ hsu (fun j hj => by rw [lu j hj]; exact hi.lim j hj)
      (by rw [fu, hi.value]; exact Nat.mod_lt _ Proof.Ed448.L_pos) hwu) fun v ⟨kv, mv, lv, vv⟩ => ?_
    refine wp_cmp rfl fun t ht hz => WP.block_nil ?_
    have mb : ∀ i < N, s.mem (p.setWidth 64 + BitVec.ofNat 64 i) =
        s0.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
      fun i hi' => outside2_byte hi.keeps.mem (hfar i hi') (by decide) (by omega)
    have val : fe t.mem base o = decodeLE ((bytesAt s0.mem (p.setWidth 64) N).drop k) % L := by
      rw [ht.mem, vv, wu, fu, hi.value, mod_fold, mb k (by omega), mb (k + 1) (by omega),
        decode_drop2 _ _ hk]
    have keep : LoopKeep base o s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem]; exact (outside2_W mu).trans (outside2_step mv)⟩
    have c10 : t.gpr .ebp = BitVec.ofNat 32 k := by
      rw [ht.gpr, kv.1 _ (by decide), cu]
    have zt : t.zf = some (decide (k = 0)) :=
      cmp_zero (by omega) (by rw [kv.1 _ (by decide), cu]) hz
    by_cases k0 : k = 0
    · subst k0
      refine .inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true], keep,
        by rw [ht.mem]; exact lv, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by simp only [eval, zt, decide_eq_false k0, Option.map_some, Bool.not_false], k,
        by omega, ⟨by omega, by omega, by have := hi.even; omega, c10, by rw [ht.mem]; exact lv, val,
          keep⟩⟩
  · exact ⟨hn0, hle, heven, hc, hl, hv, LoopKeep.refl _ _ _⟩

/-! ## The product's limbs -/

theorem ACC_eq : Impl.X448.X86.ACC = 3584 := rfl

theorem readLimb_ok {s : State} {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 56)
    (hc : s.gpr .ebp = BitVec.ofNat 32 (4 * (j + 1))) :
    WP isa (.block readLimb) s fun t =>
      Keeps [.eax, .edx, .ebp] s t ∧ Outside base W 4 s.mem t.mem ∧
      t.gpr .ebp = BitVec.ofNat 32 (4 * j) ∧
      word t.mem base W = word s.mem base (Impl.X448.X86.ACC + 4 * j) := by
  have hA := ACC_eq
  have hfit := hs.nowrap
  unfold readLimb
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun s1 u1 _ => ?_
  refine wp_mov rfl fun s2 u2 => wp_alu (Or.inl rfl) rfl fun s3 u3 _ => ?_
  have e1 : s1.gpr .ebp = BitVec.ofNat 32 (4 * j) := by
    rw [u1.gpr]
    change s.gpr .ebp - BitVec.ofNat 32 4 = _
    rw [hc, show 4 * (j + 1) = 4 * j + 4 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e3 : s3.gpr .edx = s.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [u3.gpr]
    change s2.gpr .edx + s2.gpr .ebp = _
    rw [u2.gpr, u2.other .ebp (by decide), u1.other .edi (by decide), e1]
  have hs3 := ((hs.of_upd u1 (by decide)).of_upd u2 (by decide)).of_upd u3 (by decide)
  refine wp_load (a := off base (Impl.X448.X86.ACC + 4 * j))
    (by
      change addr (s3.gpr .edx) Impl.X448.X86.ACC = _
      rw [e3, addr_add2 _ (by omega), hs.edi, Nat.add_comm])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hs.read (by omega)) fun s4 u4 => ?_
  refine store_ok (hs3.of_upd u4 (by decide)) (by simp only [W]; omega) fun s5 u5 =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest _))))
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact writeW_outside _ _ _ (by simp only [W]; omega)
  · rw [u5.gpr, u4.other .ebp (by decide), u3.other .ebp (by decide), u2.other .ebp (by decide), e1]
  · rw [u5.mem, word, Mem.readW_writeW_self32, u4.gpr, u3.mem, u2.mem, u1.mem]

/-- After the steps from the top limb down to limb `j`. -/
structure LimbInv (base : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  positive : 0 < j
  bound : j ≤ 56
  counter : s.gpr .ebp = BitVec.ofNat 32 (4 * j)
  lim : Bounded s.mem base RA
  value : fe s.mem base RA = accFrom (limbs s0.mem base Impl.X448.X86.ACC) j % L
  keeps : LoopKeep base RA s0 s

theorem limbLoop_ok {s0 : State} {base : Addr} (hs : Scr s0 base)
    (hacc : ∀ j < 56, limbs s0.mem base Impl.X448.X86.ACC j < radix)
    (hc : s0.gpr .ebp = BitVec.ofNat 32 (4 * 56)) (hl : Bounded s0.mem base RA)
    (hv : fe s0.mem base RA = 0) :
    WP isa (.loop (.block limbStep) .ne) s0 fun t => LoopKeep base RA s0 t ∧
      Bounded t.mem base RA ∧
      fe t.mem base RA = valN (limbs s0.mem base Impl.X448.X86.ACC) 56 % L := by
  have hA := ACC_eq
  have ho : Buf RA := ⟨by decide, by decide⟩
  apply WP.loop (LimbInv base s0) (n := 56)
  · intro n s hi
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by have := hi.positive; omega⟩
    have hj : j < 56 := hi.bound
    have hss : Scr s base := hs.of_keeps hi.keeps.regs (by decide)
    have la : ∀ i < 56, limbs s.mem base Impl.X448.X86.ACC i =
        limbs s0.mem base Impl.X448.X86.ACC i := fun i hi' =>
      congrArg BitVec.toNat (hi.keeps.mem.word (Or.inr (by simp only [W]; omega))
        (Or.inr (by simp only [RA]; omega)) (by omega))
    unfold limbStep
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (readLimb_ok hss hj hi.counter) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hsu : Scr u base := hss.of_keeps ku (by decide)
    have hwu : (word u.mem base W).toNat < radix := by
      rw [wu]; change limbs s.mem base Impl.X448.X86.ACC j < _; rw [la j hj]; exact hacc j hj
    have lu : ∀ i < 28, limbs u.mem base RA i = limbs s.mem base RA i :=
      fun i hi' => mu.limbs (Or.inr (by simp only [W, RA]; omega)) (by simp only [RA]; omega) hi'
    have fu : fe u.mem base RA = fe s.mem base RA := valN_congr lu
    rw [WP.block_append_iff]
    refine WP.mono (step_ok ho hsu (fun i hi' => by rw [lu i hi']; exact hi.lim i hi')
      (by rw [fu, hi.value]; exact Nat.mod_lt _ Proof.Ed448.L_pos) hwu) fun v ⟨kv, mv, lv, vv⟩ => ?_
    refine wp_cmp rfl fun t ht hz => WP.block_nil ?_
    have val : fe t.mem base RA = accFrom (limbs s0.mem base Impl.X448.X86.ACC) j % L := by
      rw [ht.mem, vv, wu, fu, hi.value, mod_fold, accFrom_step _ hj]
      change ((limbs s.mem base Impl.X448.X86.ACC j) + _) % L = _
      rw [la j hj]
    have keep : LoopKeep base RA s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem]; exact (outside2_W mu).trans (outside2_step mv)⟩
    have c10 : t.gpr .ebp = BitVec.ofNat 32 (4 * j) := by
      rw [ht.gpr, kv.1 _ (by decide), cu]
    have zt : t.zf = some (decide (4 * j = 0)) :=
      cmp_zero (by omega) (by rw [kv.1 _ (by decide), cu]) hz
    by_cases j0 : j = 0
    · subst j0
      refine .inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true], keep,
        by rw [ht.mem]; exact lv, ?_⟩
      rw [val, accFrom_zero]
    · refine .inr ⟨by simp only [eval, zt, decide_eq_false (by omega : ¬4 * j = 0), Option.map_some,
        Bool.not_false], j, by omega, ⟨by omega, by omega, c10, by rw [ht.mem]; exact lv, val, keep⟩⟩
  · refine ⟨by decide, by decide, hc, hl, ?_, LoopKeep.refl _ _ _⟩
    rw [hv]
    exact (Nat.zero_mod _).symm.trans (by rfl)

/-! ## The remainders the loops start from -/

theorem zeroR_ok {o : Nat} (ho : o + 112 ≤ 4096) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (zeroR o)) s fun t =>
      Keeps [.eax] s t ∧ Outside base o 112 s.mem t.mem ∧ (∀ k < 28, limbs t.mem base o k = 0) := by
  unfold zeroR
  rw [show ∀ (i : Instr) (is : List Instr), i :: is = [i] ++ is from fun _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (zeroEax_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  refine WP.mono (fill_ok (hs.of_keeps tk (by decide)) (o := o) (n := 28) (by omega) tz)
    fun u ⟨uf, um, uk⟩ => ⟨tk.trans (uk.mono (by simp)), by rw [← tm]; exact um, uf⟩

theorem Bounded_zero {m : Mem} {base : Addr} {o : Nat} (h : ∀ k < 28, limbs m base o k = 0) :
    Bounded m base o := fun k hk => by rw [h k hk]; decide

theorem fe_zero {m : Mem} {base : Addr} {o : Nat} (h : ∀ k < 28, limbs m base o k = 0) :
    fe m base o = 0 := (valN_congr h).trans (valN_zero 28)

end VG.Proof.Ed448.X86
