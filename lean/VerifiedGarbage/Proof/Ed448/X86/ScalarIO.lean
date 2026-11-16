module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarStep
public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.X448.X86.Fill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.X448.X86.Instr
public import VerifiedGarbage.Proof.X448.X86.Save
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Pack
import VerifiedGarbage.Proof.X448.X86.ByteMem
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ed448.X86.ScalarLoop`, which only this module used -/

section

/-!
# Ed448 scalar arithmetic on x86 (32-bit): the loops

The remainder of an input's bytes from the top, sixteen bits at a time
(`byteLoop_ok`), and of the product's limbs (`limbLoop_ok`), and the
remainders they start from (`zeroR_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR readBytes byteStep zeroR readLimb limbStep step)
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-- `[x + n + d]`, for `x + n + d` below `2^32`. -/
theorem addr_add2 (x : BitVec 32) {n d : Nat} (h : x.toNat + n + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 n) d = x.setWidth 64 + BitVec.ofNat 64 (n + d) := by
  rw [← addr_eq (by omega_using [h])]
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
    Outside2 base W 160 o 112 m m' := fun p h1 h2 => h p (by simp only [TF, W] at h1 ⊢; omega_using [h1]) h2

theorem outside2_W {base : Addr} {o : Nat} {m m' : Mem} (h : Outside base W 4 m m') :
    Outside2 base W 160 o 112 m m' := fun p h1 _ => h p (by simp only [W] at h1 ⊢; omega_using [h1])

/-- A byte beyond the working space, unchanged across the loops. -/
theorem outside2_byte {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : Outside2 base x nx y ny m m')
    {a : Addr} (ha : 8192 ≤ ofs base a) (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) : m' a = m a :=
  h a (Or.inr (by omega_using [ha, hx])) (Or.inr (by omega_using [ha, hy]))

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
  obtain e1 : s1.gpr .ebp = BitVec.ofNat 32 n := by
    rw [u1.gpr]
    change s.gpr .ebp - BitVec.ofNat 32 2 = _
    rw [hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  obtain e3 : s3.gpr .edx = p + BitVec.ofNat 32 n := by
    rw [u3.gpr]
    change s2.gpr .edx + s2.gpr .ebp = _
    rw [u2.gpr, u2.other .ebp (by decide), u1.other .esi (by decide), hp, e1]
  obtain m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 n)
    (by change addr (s3.gpr .edx) 0 = _; rw [e3, addr_add2 p (by omega_using [hn, hfit]), Nat.add_zero])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr n (by omega_using [hn])) fun s4 u4 => ?_
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 (n + 1))
    (by change addr (s4.gpr .edx) 1 = _; rw [u4.other .edx (by decide), e3, addr_add2 p (by omega_using [hn, hfit])])
    (by rw [u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hr (n + 1) (by omega_using [hn]))
    fun s5 u5 => ?_
  refine wp_shift (by decide) fun s6 u6 => wp_alu (Or.inl rfl) rfl fun s7 u7 _ => ?_
  obtain hs7 := ((((((hs.of_upd u1 (by decide)).of_upd u2 (by decide)).of_upd u3 (by decide)).of_upd u4
    (by decide)).of_upd u5 (by decide)).of_upd u6 (by decide)).of_upd u7 (by decide)
  refine store_ok hs7 (by simp only [W]; omega_using []) fun s8 u8 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
        ((u7.rest (by decide)).trans (u8.rest _)))))))
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, m3]
    exact writeW_outside _ _ _ (by simp only [W]; omega_using [])
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
      obtain h0 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).isLt
      obtain h1 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).isLt
      simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.shiftLeft_eq, BitVec.toNat_ofNat]
      omega_using []
    obtain hw : (word s8.mem base W) = s7.gpr .eax := by
      rw [u8.mem, Proof.X448.X86.word, Mem.readW_writeW_self32]
    rw [hw, value]
    obtain h0 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 n)).isLt
    obtain h1 := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (n + 1))).isLt
    exact toNat_imm (by omega_using [])

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
  obtain hN : N ≤ 2 ^ 32 := by omega_using [hfit]
  apply WP.loop (ByteInv base o N (p.setWidth 64) s0) (n := n0)
  · intro n s hi
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := hi.even; have := hi.positive; omega_arith⟩
    have hk : k + 2 ≤ N := hi.bound
    obtain hss : Scr s base := hs.of_keeps hi.keeps.regs (by decide)
    obtain hps : s.gpr .esi = p := (hi.keeps.regs.1 _ (by decide)).trans hp
    obtain hrs : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1 := by
      rw [hi.keeps.regs.2.1, hi.keeps.regs.2.2]; exact hread
    unfold byteStep
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (readBytes_ok hss hk hps hfit hi.counter hrs) fun u ⟨ku, mu, cu, wu⟩ => ?_
    obtain hsu : Scr u base := hss.of_keeps ku (by decide)
    obtain hwu : (word u.mem base W).toNat < radix := by
      rw [wu]
      have := (s.mem (p.setWidth 64 + BitVec.ofNat 64 k)).isLt
      have := (s.mem (p.setWidth 64 + BitVec.ofNat 64 (k + 1))).isLt
      simp only [radix]
      omega_using []
    obtain lu : ∀ j < 28, limbs u.mem base o j = limbs s.mem base o j :=
      fun j hj => mu.limbs (Or.inr (by simp only [W, TF] at ho1 ⊢; omega_using [ho1])) (by omega_using [ho2]) hj
    obtain fu : fe u.mem base o = fe s.mem base o := valN_congr lu
    rw [WP.block_append_iff]
    refine WP.mono (step_ok ⟨ho1, ho2⟩ hsu (fun j hj => by rw [lu j hj]; exact hi.lim j hj)
      (by rw [fu, hi.value]; exact Nat.mod_lt _ Proof.Ed448.L_pos) hwu) fun v ⟨kv, mv, lv, vv⟩ => ?_
    refine wp_cmp rfl fun t ht hz => WP.block_nil ?_
    obtain mb : ∀ i < N, s.mem (p.setWidth 64 + BitVec.ofNat 64 i) =
        s0.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
      fun i hi' => outside2_byte hi.keeps.mem (hfar i hi') (by decide) (by omega_using [ho2])
    obtain val : fe t.mem base o = decodeLE ((bytesAt s0.mem (p.setWidth 64) N).drop k) % L := by
      rw [ht.mem, vv, wu, fu, hi.value, mod_fold, mb k (by omega_using [hk]), mb (k + 1) (by omega_using [hk]),
        decode_drop2 _ _ hk]
    have keep : LoopKeep base o s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem]; exact (outside2_W mu).trans (outside2_step mv)⟩
    obtain c10 : t.gpr .ebp = BitVec.ofNat 32 k := by
      rw [ht.gpr, kv.1 _ (by decide), cu]
    obtain zt : t.zf = some (decide (k = 0)) :=
      cmp_zero (by omega_using [hfit, hk]) (by rw [kv.1 _ (by decide), cu]) hz
    by_cases k0 : k = 0
    · subst k0
      refine .inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true], keep,
        by rw [ht.mem]; exact lv, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by simp only [eval, zt, decide_eq_false k0, Option.map_some, Bool.not_false], k,
        by omega_using [], ⟨by omega_using [k0], by omega_using [hk], by have := hi.even; omega_using [this], c10, by rw [ht.mem]; exact lv, val,
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
  obtain e1 : s1.gpr .ebp = BitVec.ofNat 32 (4 * j) := by
    rw [u1.gpr]
    change s.gpr .ebp - BitVec.ofNat 32 4 = _
    rw [hc, show 4 * (j + 1) = 4 * j + 4 by omega_using [], BitVec.ofNat_add, BitVec.add_sub_cancel]
  obtain e3 : s3.gpr .edx = s.gpr .edi + BitVec.ofNat 32 (4 * j) := by
    rw [u3.gpr]
    change s2.gpr .edx + s2.gpr .ebp = _
    rw [u2.gpr, u2.other .ebp (by decide), u1.other .edi (by decide), e1]
  obtain hs3 := ((hs.of_upd u1 (by decide)).of_upd u2 (by decide)).of_upd u3 (by decide)
  refine wp_load (a := off base (Impl.X448.X86.ACC + 4 * j))
    (by
      change addr (s3.gpr .edx) Impl.X448.X86.ACC = _
      rw [e3, addr_add2 _ (by omega_using [hj, hA, hfit]), hs.edi, Nat.add_comm])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hs.read (by omega_using [hj, hA])) fun s4 u4 => ?_
  refine store_ok (hs3.of_upd u4 (by decide)) (by simp only [W]; omega_using []) fun s5 u5 =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest _))))
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact writeW_outside _ _ _ (by simp only [W]; omega_using [])
  · rw [u5.gpr, u4.other .ebp (by decide), u3.other .ebp (by decide), u2.other .ebp (by decide), e1]
  · rw [u5.mem, Proof.X448.X86.word, Mem.readW_writeW_self32, u4.gpr, u3.mem, u2.mem, u1.mem]

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
  obtain ho : Buf RA := ⟨by decide, by decide⟩
  apply WP.loop (LimbInv base s0) (n := 56)
  · intro n s hi
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by have := hi.positive; omega_using [this]⟩
    have hj : j < 56 := hi.bound
    obtain hss : Scr s base := hs.of_keeps hi.keeps.regs (by decide)
    obtain la : ∀ i < 56, limbs s.mem base Impl.X448.X86.ACC i =
        limbs s0.mem base Impl.X448.X86.ACC i := fun i hi' =>
      congrArg BitVec.toNat (hi.keeps.mem.word (Or.inr (by simp only [W]; omega_using [hA]))
        (Or.inr (by simp only [RA]; omega_using [hA])) (by omega_using [hA, hi']))
    unfold limbStep
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (readLimb_ok hss hj hi.counter) fun u ⟨ku, mu, cu, wu⟩ => ?_
    obtain hsu : Scr u base := hss.of_keeps ku (by decide)
    obtain hwu : (word u.mem base W).toNat < radix := by
      rw [wu]; change limbs s.mem base Impl.X448.X86.ACC j < _; rw [la j hj]; exact hacc j hj
    obtain lu : ∀ i < 28, limbs u.mem base RA i = limbs s.mem base RA i :=
      fun i hi' => mu.limbs (Or.inr (by simp only [W, RA]; omega_using [])) (by simp only [RA]; omega_using []) hi'
    obtain fu : fe u.mem base RA = fe s.mem base RA := valN_congr lu
    rw [WP.block_append_iff]
    refine WP.mono (step_ok ho hsu (fun i hi' => by rw [lu i hi']; exact hi.lim i hi')
      (by rw [fu, hi.value]; exact Nat.mod_lt _ Proof.Ed448.L_pos) hwu) fun v ⟨kv, mv, lv, vv⟩ => ?_
    refine wp_cmp rfl fun t ht hz => WP.block_nil ?_
    obtain val : fe t.mem base RA = accFrom (limbs s0.mem base Impl.X448.X86.ACC) j % L := by
      rw [ht.mem, vv, wu, fu, hi.value, mod_fold, accFrom_step _ hj]
      change ((limbs s.mem base Impl.X448.X86.ACC j) + _) % L = _
      rw [la j hj]
    have keep : LoopKeep base RA s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem]; exact (outside2_W mu).trans (outside2_step mv)⟩
    obtain c10 : t.gpr .ebp = BitVec.ofNat 32 (4 * j) := by
      rw [ht.gpr, kv.1 _ (by decide), cu]
    obtain zt : t.zf = some (decide (4 * j = 0)) :=
      cmp_zero (by omega_using [hj]) (by rw [kv.1 _ (by decide), cu]) hz
    by_cases j0 : j = 0
    · subst j0
      refine .inl ⟨by simp only [eval, zt, decide_true, Option.map_some, Bool.not_true], keep,
        by rw [ht.mem]; exact lv, ?_⟩
      rw [val, accFrom_zero]
    · refine .inr ⟨by simp only [eval, zt, decide_eq_false (by omega_using [j0] : ¬4 * j = 0), Option.map_some,
        Bool.not_false], j, by omega_using [], ⟨by omega_using [j0], by omega_using [hj], c10, by rw [ht.mem]; exact lv, val, keep⟩⟩
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
  refine WP.mono (fill_ok (hs.of_keeps tk (by decide)) (o := o) (n := 28) (by omega_using [ho]) tz)
    fun u ⟨uf, um, uk⟩ => ⟨tk.trans (uk.mono (by simp)), by rw [← tm]; exact um, uf⟩

theorem Bounded_zero {m : Mem} {base : Addr} {o : Nat} (h : ∀ k < 28, limbs m base o k = 0) :
    Bounded m base o := fun k hk => by rw [h k hk]; decide

theorem fe_zero {m : Mem} {base : Addr} {o : Nat} (h : ∀ k < 28, limbs m base o k = 0) :
    fe m base o = 0 := (valN_congr h).trans (valN_zero 28)

end VG.Proof.Ed448.X86

end

end


/-!
# Ed448 scalar arithmetic on x86 (32-bit): entry and exit

The cdecl arguments (`Args`: they stay on the stack, which the code does not
write, `Args.load`), the callee-saved registers saved in the working space
(`save_ok`, as X448 saves them), the remainders of the inputs
(`reduce114_ok`, `reduce57_ok`), and the result: the remainder's limbs as 56
bytes and a zero byte, its encoding, then the registers restored
(`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR zeroR reduce114 reduce57 packLimb finish)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-! ## The arguments -/

/-- The `n` cdecl arguments of 4 bytes on the stack, readable and disjoint
from the working space, the argument `sc`. -/
structure Args (s₀ : State) (n sc : Nat) : Prop where
  in_rd : (⟨argAddr s₀ 0, 4 * n⟩ : Region) ∈ s₀.rd
  sp_fit : (s₀.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  sc_lt : sc < n
  sc_in : scR (arg s₀ sc) ∈ s₀.wr
  sc_fit : (arg s₀ sc).toNat + 8192 ≤ 2 ^ 32
  args_sc : (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint (scR (arg s₀ sc))
  ret_sc : (retR s₀).Disjoint (scR (arg s₀ sc))

namespace Args
variable {s₀ : State} {n sc : Nat} (hp : Args s₀ n sc)
include hp

theorem arg_contains {i : Nat} (hi : i < n) :
    (⟨argAddr s₀ 0, 4 * n⟩ : Region).Contains (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.X25519.X86.sub_contains (x := s₀.gpr .esp) (a := 4) (k := 4 * n)
    (by have := hp.sp_fit; omega_arith) (by omega_arith) (by omega_arith) (by decide)

/-- An argument, in memory the code has written only in the working space. -/
theorem arg_same {m : Mem} (hf : Frame [scR (arg s₀ sc)] s₀.mem m) {i : Nat} (hi : i < n) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (hp.arg_contains hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

/-- An argument, in memory the code has written only in regions apart from
the arguments. -/
theorem arg_frame {m : Mem} {rs : List Region} (hf : Frame rs s₀.mem m)
    (hd : ∀ r ∈ rs, (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint r) {i : Nat} (hi : i < n) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (hp.arg_contains hi) hd (by decide)

/-- `load`, with the memory changed only in regions apart from the arguments. -/
theorem loadF {s : State} (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd)
    (hw : s.wr = s₀.wr) {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint r)
    {i : Nat} (hi : i < n) {d : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t d (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem (Impl.X448.X86.at_ .esp (4 + 4 * i))) :: is)) s Q := by
  refine wp_load (a := addr (s₀.gpr .esp) (4 + 4 * i))
    (by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp])
    (by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩) fun t ht => ?_
  rw [hp.arg_frame hf hd hi] at ht
  exact k t ht

theorem load {s : State} (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd)
    (hw : s.wr = s₀.wr) (hm : Outside ((arg s₀ sc).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < n) {d : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Upd s t d (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem (Impl.X448.X86.at_ .esp (4 + 4 * i))) :: is)) s Q := by
  refine wp_load (a := addr (s₀.gpr .esp) (4 + 4 * i))
    (by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp])
    (by rw [hr, hw]; exact ⟨_, List.mem_append_left _ hp.in_rd, hp.arg_contains hi⟩) fun t ht => ?_
  rw [hp.arg_same hm.frame hi] at ht
  exact k t ht

end Args

/-! ## Saving the callee-saved registers -/

theorem save_ok {s : State} {n sc : Nat} (hp : Args s n sc) :
    WP isa (.block (Impl.Ed448.X86.save (4 + 4 * sc))) s fun t =>
      Scr t ((arg s sc).setWidth 64) ∧ Saved ((arg s sc).setWidth 64) s.gpr t.mem ∧
      Outside ((arg s sc).setWidth 64) 0 16 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (Impl.X448.X86.at_ .esp (4 + 4 * sc))) ::
    (Spill.saveCode .eax savedSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine hp.load rfl rfl rfl (Outside.refl _ _ _ _) hp.sc_lt fun t ht => ?_
  have hfit := hp.sc_fit
  refine Spill.save_ofNat_ok savedSlots (n := 16) (by decide) (by rw [ht.gpr]; omega_arith)
    (fun p h => by rw [ht.gpr, ht.wr]; exact ⟨_, hp.sc_in, contains_sc (by have := savedSlots_bound p h; omega_arith)⟩)
    fun u hu => ?_
  obtain hm : u.mem = Spill.saveMem s.mem (off ((arg s sc).setWidth 64)) s.gpr savedSlots := by
    rw [hu.mem, ht.gpr, ht.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => ht.other _ (by revert p h; decide)
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (ht.rest (by decide)).trans
    (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : Keeps [.eax, .edi] t u) |>.trans (hv.rest (by decide))⟩
  · rw [hv.gpr, hu.gpr, ht.gpr]
  · rw [hv.wr, hu.wr, ht.wr]; exact hp.sc_in
  · rw [hv.gpr, hu.gpr, ht.gpr]; exact hfit
  · rw [hv.mem, hm]; exact Spill.saveMem_saved_ofNat _ _ _ (n := 16) (by decide) (by decide)
  · rw [hv.mem, hm]
    exact Outside.of_frame (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      Offset.contains_base _ (savedSlots_bound p h) (by have := savedSlots_bound p h; omega_arith))

/-! ## The remainders of the inputs -/

theorem init114_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (zeroR o ++ ([.mov .ebp (.imm 114)] : List Instr))) s fun v =>
      LoopKeep base o s v ∧ v.gpr .ebp = BitVec.ofNat 32 114 ∧ Bounded v.mem base o ∧
        fe v.mem base o = 0 := by
  rw [WP.block_append_iff]
  refine WP.mono (zeroR_ok ho.2 hs) fun u ⟨ku, fu, zu⟩ =>
    wp_mov rfl fun v hv => WP.block_nil
      ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by
        rw [hv.mem]; exact fun p _ h2 => fu p h2⟩,
        hv.gpr, by rw [hv.mem]; exact Bounded_zero zu, by rw [hv.mem]; exact fe_zero zu⟩

/-- The input's bytes, readable and beyond the working space. -/
structure Input (s : State) (base : Addr) (p : BitVec 32) (N : Nat) : Prop where
  fit : p.toNat + N ≤ 2 ^ 32
  read : ∀ i < N, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1
  far : ∀ i < N, 8192 ≤ ofs base (p.setWidth 64 + BitVec.ofNat 64 i)

theorem Input.of_keeps {s t : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N)
    {rs : List Reg} (hk : Keeps rs s t) : Input t base p N :=
  ⟨h.fit, by rw [hk.2.1, hk.2.2]; exact h.read, h.far⟩

/-- An input's bytes across a change of the working space. -/
theorem Input.bytes {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (h : Input s base p N)
    {m m' : Mem} (hm : Outside base 0 8192 m m') :
    bytesAt m' (p.setWidth 64) N = bytesAt m (p.setWidth 64) N := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => hm _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact h.far i hi

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega_arith)
    (by omega_arith)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega_arith

/-- The working space lies beyond a region of `n` bytes disjoint from it. -/
theorem far_out {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩)
    {i : Nat} (hi : i < 8192) : n ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192)
    (by omega_arith) (by omega_arith))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ n
  omega_arith

theorem Input.of_region {s : State} {base : Addr} {p : BitVec 32} {N : Nat} (hfit : p.toNat + N ≤ 2 ^ 32)
    (hin : (⟨p.setWidth 64, N⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : (⟨p.setWidth 64, N⟩ : Region).Disjoint ⟨base, 8192⟩) : Input s base p N :=
  ⟨hfit, fun i hi => ⟨_, hin, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    fun i hi => VG.Proof.Ed448.X86.far hd hi (by omega_arith)⟩

theorem LoopKeep.whole {base : Addr} {o : Nat} {s t : State} (h : LoopKeep base o s t)
    (ho : o + 112 ≤ 8192) : Outside base 0 8192 s.mem t.mem :=
  fun p hp => h.mem p (by simp only [W]; omega_arith) (by omega_arith)

theorem reduce114_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 114) :
    WP isa (reduce114 o) s fun t => LoopKeep base o s t ∧ Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s.mem (p.setWidth 64) 114) % L := by
  unfold reduce114
  refine WP.seq (WP.mono (init114_ok ho hs) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  obtain mb := hin.bytes (kv.whole (by have := ho.2; omega_arith))
  refine WP.mono (byteLoop_ok (N := 114) ho (hs.of_keeps kv.regs (by decide))
    ((kv.regs.1 _ (by decide)).trans hp) hin.fit (by rw [kv.regs.2.1, kv.regs.2.2]; exact hin.read)
    hin.far (n0 := 114) (by decide) (by decide) (by decide) cv lv
    (by rw [vv, List.drop_eq_nil_of_le (by rw [Proof.Ed448.bytesAt_length]),
      show decodeLE [] = 0 from rfl, Nat.zero_mod]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

theorem init57_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 57) :
    WP isa (.block (zeroR o ++ ([.movzx8 .eax (Impl.X448.X86.at_ .esi 56), Impl.X448.X86.st .eax o,
      .mov .ebp (.imm 56)] : List Instr))) s fun v =>
      LoopKeep base o s v ∧ v.gpr .ebp = BitVec.ofNat 32 56 ∧ Bounded v.mem base o ∧
      fe v.mem base o = decodeLE ((bytesAt s.mem (p.setWidth 64) 57).drop 56) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  rw [WP.block_append_iff]
  refine WP.mono (zeroR_ok ho2 hs) fun u ⟨ku, fu, zu⟩ => ?_
  obtain hpu : u.gpr .esi = p := (ku.1 _ (by decide)).trans hp
  obtain hsu := hs.of_keeps ku (by decide)
  refine wp_load8 (a := p.setWidth 64 + BitVec.ofNat 64 56)
    (by change addr (u.gpr .esi) 56 = _; rw [hpu]; exact addr_eq (by have := hin.fit; omega_arith))
    (by rw [ku.2.1, ku.2.2]; exact hin.read 56 (by decide)) fun u1 v1 => ?_
  refine store_ok (hsu.of_upd v1 (by decide)) (by omega_arith) fun u2 v2 => wp_mov rfl fun v hv =>
    WP.block_nil ?_
  obtain byte : u.mem (p.setWidth 64 + BitVec.ofNat 64 56) = s.mem (p.setWidth 64 + BitVec.ofNat 64 56) :=
    fu _ (Or.inr (by have := hin.far 56 (by decide); omega_arith))
  obtain m2 : v.mem = u.mem.writeW (off base (o + 4 * 0))
      ((s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).setWidth 32) := by
    rw [hv.mem, v2.mem, v1.gpr, v1.mem, byte]; rfl
  obtain lv : ∀ k < 28, limbs v.mem base o k =
      if k = 0 then (s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).toNat else 0 := by
    intro k hk
    change (word v.mem base (o + 4 * k)).toNat = _
    rw [m2, word_write u.mem base (by omega_arith) (by omega_arith)]
    by_cases k0 : k = 0
    · rw [ite_eq_left k0, ite_eq_left k0, BitVec.toNat_setWidth_of_le (by decide)]
    · rw [ite_eq_right k0, ite_eq_right k0]; exact zu k hk
  obtain hlt := (s.mem (p.setWidth 64 + BitVec.ofNat 64 56)).isLt
  refine ⟨⟨(ku.mono (by decide)).trans ((v1.rest (by decide)).trans ((v2.rest _).trans
    (hv.rest (by decide)))), ?_⟩, hv.gpr, fun k hk => ?_, ?_⟩
  · rw [m2]
    intro q _ h2
    rw [writeW_outside _ _ _ (by omega_arith) q (by omega_arith)]
    exact fu q h2
  · rw [lv k hk]; split
    · simp only [radix]; omega_arith
    · decide
  · rw [decode_drop1 _ _ (by decide : 56 + 1 = 57)]
    obtain hL : 256 < L := by decide +kernel
    rw [Nat.mod_eq_of_lt (by omega_arith)]
    show valN (limbs v.mem base o) 28 = _
    rw [show (28 : Nat) = 1 + 27 from rfl, valN_split,
      valN_congr (n := 27) (g := fun _ => 0) (fun k hk => by rw [lv _ (by omega_arith), ite_eq_right (by omega_arith)]),
      valN_zero]
    simp only [valN, lv 0 (by decide), ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.add_zero]

theorem reduce57_ok {o : Nat} (ho : Buf o) {s : State} {base : Addr} (hs : Scr s base)
    {p : BitVec 32} (hp : s.gpr .esi = p) (hin : Input s base p 57) :
    WP isa (reduce57 o) s fun t => LoopKeep base o s t ∧ Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s.mem (p.setWidth 64) 57) % L := by
  unfold reduce57
  refine WP.seq (WP.mono (init57_ok ho hs hp hin) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  obtain mb := hin.bytes (kv.whole (by have := ho.2; omega_arith))
  refine WP.mono (byteLoop_ok (N := 57) ho (hs.of_keeps kv.regs (by decide))
    ((kv.regs.1 _ (by decide)).trans hp) hin.fit (by rw [kv.regs.2.1, kv.regs.2.2]; exact hin.read)
    hin.far (n0 := 56) (by decide) (by decide) (by decide) cv lv (by rw [vv, mb]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

/-! ## The result -/

/-- Writes to the output preserve a word of the disjoint working space. -/
theorem out_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m')
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, n ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (by have := hfar (d + i) (by omega_arith); simp only [off] at this; omega_arith))

theorem packLimb_ok {s : State} {base p : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o) {i : Nat} (hi : i < 28) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (off p (2 * i + j)) 1) :
    WP isa (.block (packLimb o i)) s fun t =>
      decoded t.mem p i = limbs s.mem base o i ∧ Outside p (2 * i) 2 s.mem t.mem ∧ Keeps [.eax] s t := by
  obtain ea : ∀ j < 2, addr (s.gpr .esi) (2 * i + j) = off p (2 * i + j) := by
    intro j hj; rw [addr_eq (by omega_arith), hp]
  unfold packLimb
  refine load_ok hs (by omega_arith) fun t ht => ?_
  refine wp_store8 (a := off p (2 * i))
    (by change addr (t.gpr .esi) _ = _; rw [ht.other .esi (by decide)]; exact ea 0 (by decide))
    (by rw [ht.wr]; exact hw 0 (by decide)) fun u hu => ?_
  refine wp_shift (by decide) fun v hv => ?_
  refine wp_store8 (a := off p (2 * i + 1))
    (by change addr (v.gpr .esi) _ = _
        rw [hv.other .esi (by decide), hu.gpr, ht.other .esi (by decide)]; exact ea 1 (by decide))
    (by rw [hv.wr, hu.wr, ht.wr]; exact hw 1 (by decide)) fun w hw' => WP.block_nil ⟨?_, ?_, ?_⟩
  · have hm : w.mem = packMem s.mem p i (word s.mem base (o + 4 * i)) := by
      rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
    rw [hm]; exact packMem_decoded _ _ hi _ (hb i hi)
  · have hm : w.mem = packMem s.mem p i (word s.mem base (o + 4 * i)) := by
      rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
    rw [hm]; exact packMem_outside _ _ hi _
  · exact ((ht.rest (by decide)).trans ((hu.rest _).trans
      ((hv.rest (by decide)).trans (hw'.rest _))))

theorem packAll_ok {s : State} {base p : Addr} (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 57 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 28).flatMap (packLimb o))) s fun t =>
      (∀ i < 28, decoded t.mem p i = limbs s.mem base o i) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, decoded t.mem p i = limbs s.mem base o i) ∧ Outside p 0 (2 * n) s.mem t.mem ∧
      Keeps [.eax] s t
  obtain st : ∀ n t, n < 28 → inv n t → WP isa (.block (packLimb o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain eq : ∀ j < 28, limbs t.mem base o j = limbs s.mem base o j := by
      intro j hj
      exact congrArg BitVec.toNat (out_word tm (by omega_arith) fun i hi => Nat.le_trans (by omega_arith) (hfar i hi))
    obtain tb : Bounded t.mem base o := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (packLimb_ok (p := p) (hs.of_keeps tk (by decide)) ho tb hn
      (by rw [tk.1 _ (by decide)]; exact hp) (by rw [tk.1 _ (by decide)]; exact hfit)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega_arith))) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, (tm.mono (by decide) (by omega_arith)).trans (um.mono (by omega_arith) (by omega_arith)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans (eq n hn)
    · have byte : ∀ j < 2, u.mem (off p (2 * i + j)) = t.mem (off p (2 * i + j)) := by
        intro j hj
        exact um _ (Or.inl (by rw [ofs_off' p (by omega_arith)]; omega_arith))
      simp only [decoded, byteN]
      obtain b0 := byte 0 (by decide)
      obtain b1 := byte 1 (by decide)
      simp only [off, Nat.add_zero] at b0 b1
      rw [b0, b1]
      exact tf i (by omega_arith)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega_arith, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The registers `finish` changes. -/
def finishRegs : List Reg := [.eax, .ebx, .esi, .edi, .ebp]

/-- `finish o`: the remainder at `o` as 57 bytes at the output (the argument
0), and the callee-saved registers restored. -/
theorem finish_ok {s₀ s : State} {n sc : Nat} (hp : Args s₀ n sc) (h0 : 0 < n)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ sc).setWidth 64 = base)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base) {o : Nat} (ho : o + 112 ≤ 4096)
    (hb : Bounded s.mem base o)
    (hout : (⟨(arg s₀ 0).setWidth 64, 57⟩ : Region) ∈ s₀.wr) (hofit : (arg s₀ 0).toNat + 57 ≤ 2 ^ 32)
    (hfar : ∀ j < 8192, 57 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j))
    (sv : Saved base s₀.gpr s.mem) :
    WP isa (.block (finish o)) s fun t =>
      (∀ p ∈ savedSlots, t.gpr p.1 = s₀.gpr p.1) ∧ Keeps finishRegs s t ∧
      Outside ((arg s₀ 0).setWidth 64) 0 57 s.mem t.mem ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 = encodeLE 57 (fe s.mem base o) := by
  unfold finish
  simp only [List.cons_append, List.append_assoc]
  refine hp.load hsp hr hwr (hbase ▸ hm) h0 fun v hv => ?_
  generalize hP : (arg s₀ 0).setWidth 64 = P at hout hfar ⊢
  obtain hvs := hs.of_upd hv (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (packAll_ok hvs ho (hv.mem ▸ hb) (by rw [hv.gpr, hP]) (by rw [hv.gpr]; exact hofit)
    (by intro j hj; rw [hv.wr, hwr]; exact ⟨_, hout, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    hfar) fun w ⟨wd, wm, wk⟩ => ?_
  refine wp_mov rfl fun x hx => ?_
  obtain hxs : x.gpr .esi = arg s₀ 0 := by
    rw [hx.other .esi (by decide), wk.1 _ (by decide), hv.gpr]
  refine wp_store8 (a := P + BitVec.ofNat 64 56)
    (by change addr (x.gpr .esi) 56 = _; rw [hxs, addr_eq (by omega_arith), hP])
    (by rw [hx.wr, wk.2.2, hv.wr, hwr]; exact ⟨_, hout, Offset.contains_base _ (by decide) (by decide)⟩)
    fun y hy => ?_
  obtain hm2 : y.mem = w.mem.writeW (P + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [hy.mem, Reg8.reg, hx.gpr, hx.mem]; rfl
  obtain ym : Outside P 0 57 s.mem y.mem := by
    rw [hm2, ← hv.mem]
    intro q hq
    rw [writeW8_outside _ _ _ (by decide) (by intro e; simp only [ofs] at hq e; omega_arith)]
    exact wm q (by omega_arith)
  obtain ys := ((hvs.of_keeps wk (by decide)).of_upd hx (by decide)).of_keeps (hy.rest []) (by decide)
  obtain svy : Saved base s₀.gpr y.mem := sv.of_readW fun q hq => by
    have := savedSlots_bound q hq
    exact out_word ym (by omega_arith) hfar
  refine WP.mono (restore_ok ys svy) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, ?_, by rw [tm]; exact ym, ?_⟩
  · refine (hv.rest (by decide)).trans ((wk.mono (by decide)).trans ((hx.rest (by decide)).trans
      ((hy.rest _).trans (tk.mono ?_))))
    intro r hr; simp only [restoreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [tm]
    refine encode_57 hb (fun k hk => ?_) ?_
    · have e := wd k hk
      rw [hv.mem] at e
      rw [← e]
      simp only [decoded, byteN]
      obtain b : ∀ i < 56, y.mem (P + BitVec.ofNat 64 i) = w.mem (P + BitVec.ofNat 64 i) := fun i hi => by
        rw [hm2, writeW8_outside _ _ _ (by decide) (by rw [ofs_off' P (by omega_arith)]; omega_arith)]
      rw [b (2 * k) (by omega_arith), b (2 * k + 1) (by omega_arith)]
    · rw [hm2, writeW8_apply, ite_eq_left rfl]

end VG.Proof.Ed448.X86
