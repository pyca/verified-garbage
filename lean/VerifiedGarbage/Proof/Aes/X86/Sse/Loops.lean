module

public import VerifiedGarbage.Proof.Aes.X86.Sse.Rounds
import VerifiedGarbage.Proof.Aes.Vector
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Reduce

/-!
# AES in SSE2 registers on x86 (32-bit): the loops over the blocks of a pass

The blocks of a pass are copied to the slots and back (`copy_loop`), or the
slots XORed with the data (`xor_loop`), a block at a time. What such a loop
leaves in memory is `patch`: its destination's bytes replaced, and nothing
else.
-/

@[expose] public section

namespace VG.Proof.Aes.X86.Sse

open VG VG.X86 VG.Impl.Aes.X86.Sse VG.Proof.Aes
open VG.Impl.Aes.X86 (sb at_ argOp movI addI subI addR subR dbl movR)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_sub wp_subi wp_ldm wp_stm wp_cmpi wp_test
  toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-! ## Memory with some bytes replaced -/

/-- `m` with the `n` bytes at `a` replaced by `v 0, v 1, …`. -/
def patch (m : Mem) (a : Addr) (n : Nat) (v : Nat → Byte) : Mem :=
  fun x => if (x - a).toNat < n then v (x - a).toNat else m x

theorem patch_zero (m : Mem) (a : Addr) (v : Nat → Byte) : patch m a 0 v = m := by
  funext x; simp [patch]

theorem patch_at {m : Mem} {a : Addr} {n : Nat} {v : Nat → Byte} {i : Nat} (hi : i < n) (hn : n ≤ 2 ^ 64) :
    patch m a n v (a + BitVec.ofNat 64 i) = v i := by
  rw [patch, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hn]), ite_eq_left hi]

theorem patch_frame (m : Mem) (a : Addr) (n : Nat) (v : Nat → Byte) : Frame [⟨a, n⟩] m (patch m a n v) := by
  intro x hx
  have h := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h
  rw [patch, ite_eq_right (by omega_using [h])]

theorem patch_write {m : Mem} {a : Addr} {k : Nat} {v : Nat → Byte} {x : BitVec 128} (hk : 16 * k + 16 ≤ 2 ^ 64)
    (hx : ∀ i < 16, x.extractLsb' (8 * i) 8 = v (16 * k + i)) :
    (patch m a (16 * k) v).writeW (a + BitVec.ofNat 64 (16 * k)) x = patch m a (16 * (k + 1)) v := by
  funext y
  unfold Mem.writeW Mem.write patch
  have e : (y - (a + BitVec.ofNat 64 (16 * k))).toNat =
      if 16 * k ≤ (y - a).toNat then (y - a).toNat - 16 * k else 2 ^ 64 + (y - a).toNat - 16 * k := by
    rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]
    have := (y - a).isLt
    split <;> omega_arith
  have hy := (y - a).isLt
  rw [e]
  generalize (y - a).toNat = d at *
  by_cases h1 : 16 * k ≤ d
  · rw [ite_eq_left h1]
    by_cases h2 : d - 16 * k < 16
    · rw [ite_eq_left (show d - 16 * k < 128 / 8 from h2), ite_eq_left (by omega_using [h1, h2]), BitVec.setWidth_eq]
      rw [hx _ h2, Nat.add_sub_cancel' h1]
    · rw [ite_eq_right (show ¬ d - 16 * k < 128 / 8 from h2), ite_eq_right (by omega_using [h1]),
        ite_eq_right (by omega_using [h1, h2])]
  · rw [ite_eq_right h1, ite_eq_right (by omega_using [h1, hk]), ite_eq_left (by omega_using [h1]),
      ite_eq_left (by omega_using [h1])]

/-! ## Vector instructions -/

/-- `s'` is `s` with the vector register `d` set to `v`. -/
structure XUpd (s s' : State) (d : XReg) (v : BitVec 128) : Prop where
  xmm : s'.xmm d = v
  other : ∀ r, r ≠ d → s'.xmm r = s.xmm r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem XUpd.setXmm (s : State) (d : XReg) (v : BitVec 128) : XUpd s (s.setXmm d v) d v :=
  ⟨by simp [State.setXmm], fun r h => by simp [State.setXmm, h], rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {P : State → Prop}

theorem wp_ldx {d : XReg} {b : Reg} {A : BitVec 32} {o : Nat} (hb : s.gpr b = A)
    (hin : InRegions (s.rd ++ s.wr) (addr A o) 16)
    (k : ∀ s', XUpd s s' d (s.mem.readW (addr A o) 128) → WP isa (.block is) s' P) :
    WP isa (.block (.movdquLoad d ⟨b, o⟩ :: is)) s P :=
  Wp.cons (s' := s.setXmm d _) (by simp only [reduceExec, State.load128, ea_mk, hb, hin, ite_true, Option.map_some])
    (k _ (XUpd.setXmm _ _ _))

theorem wp_stx {d : XReg} {b : Reg} {A : BitVec 32} {o : Nat} (hb : s.gpr b = A)
    (hin : InRegions s.wr (addr A o) 16)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr A o) (s.xmm d)) → WP isa (.block is) s' P) :
    WP isa (.block (.movdquStore ⟨b, o⟩ d :: is)) s P := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW (addr A o) (s.xmm d) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [reduceExec, State.store128, ea_mk, hb, hin, ite_true]

theorem wp_pxor {d r : XReg} (k : ∀ s', XUpd s s' d (s.xmm d ^^^ s.xmm r) → WP isa (.block is) s' P) :
    WP isa (.block (.xop (.bin .pxor d r) :: is)) s P :=
  Wp.cons rfl (k _ (XUpd.setXmm _ _ _))

end

/-! ## How many blocks -/

theorem takeCount_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (hbp : s.gpr .ebp = BitVec.ofNat 32 n)
    {P : State → Prop} (h : ∀ s', Upd s s' .ecx (BitVec.ofNat 32 (min 8 n)) → P s') : WP isa takeCount s P := by
  refine WP.seq (wp_cmpi fun s₁ u₁ hcf _ => WP.block_nil ?_)
  rw [hbp, toNat_ofNat_lt hn, show (8 : BitVec 32).toNat = 8 from rfl] at hcf
  have fin : ∀ s₂ v, Upd s₁ s₂ .ecx v → v = BitVec.ofNat 32 (min 8 n) → P s₂ := fun s₂ v u hv =>
    h s₂ ⟨by rw [u.gpr, hv], fun r hr => by rw [u.other r hr, u₁.gpr], by rw [u.mem, u₁.mem], by rw [u.rd, u₁.rd],
      by rw [u.wr, u₁.wr], by rw [u.syms, u₁.syms]⟩
  refine WP.ite (!decide (n < 8)) (by simp [X86.eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · have : 8 ≤ n := by simpa using hb
    exact wp_movi fun s₂ u₂ => WP.block_nil (fin s₂ _ u₂ (by rw [show min 8 n = 8 by omega_using [this]]; rfl))
  · have : n < 8 := by simpa using hb
    exact wp_mov fun s₂ u₂ => WP.block_nil (fin s₂ _ u₂ (by
      rw [u₁.gpr, hbp, show min 8 n = n by omega_using [this]]))

/-! ## Copying blocks -/

theorem byte_of_readW (m : Mem) (a : Addr) {i : Nat} (hi : i < 16) :
    (m.readW a 128).extractLsb' (8 * i) 8 = m (a + BitVec.ofNat 64 i) := by
  rw [← Mem.extractLsb'_read m a (n := 16) hi]; rfl

theorem setWidth_add {A : BitVec 32} {o : Nat} (h : A.toNat + o < 2 ^ 32) :
    addr A o = A.setWidth 64 + BitVec.ofNat 64 o := addr_eq h

/-- Source bytes from `16 k` on, apart from the destination or the same, are
not yet replaced. -/
theorem patch_src {m : Mem} {A D : Addr} {n k i : Nat} {v : Nat → Byte} (hn : n ≤ 2 ^ 64) (hk : k ≤ i) (hi : i < n)
    (hsd : A = D ∨ Region.Disjoint ⟨A, n⟩ ⟨D, n⟩) :
    patch m D k v (A + BitVec.ofNat 64 i) = m (A + BitVec.ofNat 64 i) := by
  rcases hsd with rfl | h
  · rw [patch, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hn]),
      ite_eq_right (by omega_using [hk])]
  · refine patch_frame m D k v _ fun r hr hc => ?_
    simp only [List.mem_singleton] at hr; subst hr
    refine h (A + BitVec.ofNat 64 i) ?_ ?_
    · simp only [Region.Contains]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi, hn])]
      omega_using [hi]
    · simp only [Region.Contains] at hc ⊢; omega_using [hc, hk, hi]

/-- The machine during a loop: `k` of `m` blocks done. -/
structure LInv (s₀ : State) (m : Nat) (dst : Reg) (v : Nat → Byte) (regs : List Reg) (k : Nat) (s : State) : Prop where
  hk : k < m
  cnt : s.gpr .ecx = BitVec.ofNat 32 (m - k)
  ptr : ∀ r ∈ regs, s.gpr r = s₀.gpr r + BitVec.ofNat 32 (16 * k)
  other : ∀ r, r ≠ .ecx → r ∉ regs → s.gpr r = s₀.gpr r
  mem : s.mem = patch s₀.mem ((s₀.gpr dst).setWidth 64) (16 * k) v
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- After a loop. -/
structure LDone (s₀ : State) (m : Nat) (dst : Reg) (v : Nat → Byte) (regs : List Reg) (s : State) : Prop where
  ptr : ∀ r ∈ regs, s.gpr r = s₀.gpr r + BitVec.ofNat 32 (16 * m)
  other : ∀ r, r ≠ .ecx → r ∉ regs → s.gpr r = s₀.gpr r
  mem : s.mem = patch s₀.mem ((s₀.gpr dst).setWidth 64) (16 * m) v
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem loop_ok {body : List Instr} {s₀ : State} {m : Nat} {dst : Reg} {v : Nat → Byte} {regs : List Reg}
    (hm : m < 2 ^ 32) (h0 : 0 < m) (hc : s₀.gpr .ecx = BitVec.ofNat 32 m)
    (hb : ∀ k s, LInv s₀ m dst v regs k s → WP isa (.block body) s fun s' =>
      s'.gpr .ecx = BitVec.ofNat 32 (m - k) - 1 ∧ s'.zf = some (BitVec.ofNat 32 (m - k) - 1 == 0) ∧
      (∀ r ∈ regs, s'.gpr r = s₀.gpr r + BitVec.ofNat 32 (16 * (k + 1))) ∧
      (∀ r, r ≠ .ecx → r ∉ regs → s'.gpr r = s₀.gpr r) ∧
      s'.mem = patch s₀.mem ((s₀.gpr dst).setWidth 64) (16 * (k + 1)) v ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr) :
    WP isa (.loop (.block body) .ne) s₀ (LDone s₀ m dst v regs) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = m - k ∧ LInv s₀ m dst v regs k s)
    (fun n s ⟨k, hn, hi⟩ => WP.mono (hb k s hi) fun s' ⟨hcx, hz, hp, ho, hmem, hrd, hwr⟩ => ?_) m s₀
    ⟨0, rfl, h0, by rw [hc, Nat.sub_zero], fun r _ => by simp, fun _ _ _ => rfl, by rw [Nat.mul_zero, patch_zero], rfl,
      rfl⟩
  have hk := hi.hk
  have e : BitVec.ofNat 32 (m - k) - 1 = BitVec.ofNat 32 (m - (k + 1)) := Wp.sub_ofNat (b := 1) (by omega_using [hk])
  rw [e] at hcx
  rw [e, ofNat_beq_zero (by omega_using [hm])] at hz
  by_cases hlast : k + 1 = m
  · refine .inl ⟨by simp [X86.eval, hz, hlast], ?_, ho, ?_, hrd, hwr⟩
    · rw [← hlast]; exact hp
    · rw [← hlast]; exact hmem
  · exact .inr ⟨by simp [X86.eval, hz, show ¬ m - (k + 1) = 0 by omega_using [hk, hlast]], m - (k + 1),
      by omega_using [hn, hk], k + 1, rfl, by omega_using [hk, hlast], hcx, hp, ho, hmem, hrd, hwr⟩

/-- The `n` bytes of a buffer at `A` are readable or writable, a block at a time. -/
def BlocksIn (rs : List Region) (A : BitVec 32) (m : Nat) : Prop := ∀ k < m, InRegions rs (addr A (16 * k)) 16

theorem blocksIn_of {rs : List Region} {A : BitVec 32} {N a m : Nat} (hr : reg32 A N ∈ rs)
    (hfit : A.toNat + N ≤ 2 ^ 32) (h : a + 16 * m ≤ N) : BlocksIn rs (A + BitVec.ofNat 32 a) m := fun k hk => by
  rw [addr_add]; exact in_reg hr hfit (by omega_using [h, hk]) (by decide)

theorem ptr_lt {A : BitVec 32} {m k : Nat} (hf : A.toNat + 16 * m ≤ 2 ^ 32) (hk : k < m) :
    (A + BitVec.ofNat 32 (16 * k)).setWidth 64 = A.setWidth 64 + BitVec.ofNat 64 (16 * k) := by
  rw [← addr_zero, addr_add, Nat.add_zero, addr_eq (by omega_using [hf, hk])]

/-- The bytes of block `k` at `A`. -/
theorem src_bytes {s₀ : State} {m : Nat} {dst : Reg} {v : Nat → Byte} {regs : List Reg} {k : Nat} {s : State}
    (hi : LInv s₀ m dst v regs k s) {A : BitVec 32} (hf : A.toNat + 16 * m ≤ 2 ^ 32)
    (hsd : A = s₀.gpr dst ∨ Region.Disjoint ⟨A.setWidth 64, 16 * m⟩ ⟨(s₀.gpr dst).setWidth 64, 16 * m⟩)
    {i : Nat} (hi16 : i < 16) :
    (s.mem.readW (addr (A + BitVec.ofNat 32 (16 * k)) 0) 128).extractLsb' (8 * i) 8 =
      s₀.mem (A.setWidth 64 + BitVec.ofNat 64 (16 * k + i)) := by
  have hk := hi.hk
  rw [byte_of_readW _ _ hi16, addr_zero, ptr_lt hf hk, BitVec.add_assoc, ← BitVec.ofNat_add, hi.mem]
  exact patch_src (n := 16 * m) (by omega_using [hf]) (by omega_using []) (by omega_using [hk, hi16])
    (hsd.imp (fun h => by rw [h]) id)

/-- Copying `m` blocks from `src` to `dst`, apart. -/
theorem copy_loop {src dst : Reg} (h1 : src ≠ dst) (h2 : src ≠ .ecx) (h3 : dst ≠ .ecx) {s : State} {m : Nat}
    (hm : m < 2 ^ 32) (h0 : 0 < m) (hc : s.gpr .ecx = BitVec.ofNat 32 m)
    (hA : (s.gpr src).toNat + 16 * m ≤ 2 ^ 32) (hD : (s.gpr dst).toNat + 16 * m ≤ 2 ^ 32)
    (hrd : BlocksIn (s.rd ++ s.wr) (s.gpr src) m) (hwr : BlocksIn s.wr (s.gpr dst) m)
    (hsd : Region.Disjoint ⟨(s.gpr src).setWidth 64, 16 * m⟩ ⟨(s.gpr dst).setWidth 64, 16 * m⟩) :
    WP isa (.loop (.block (copyBody src dst)) .ne) s
      (LDone s m dst (fun i => s.mem ((s.gpr src).setWidth 64 + BitVec.ofNat 64 i)) [src, dst]) := by
  refine loop_ok hm h0 hc fun k t hi => ?_
  have hk := hi.hk
  refine wp_ldx (hi.ptr src (by simp)) (by rw [hi.rd, hi.wr, addr_add]; exact hrd k hk) fun s₁ u₁ => ?_
  refine wp_stx (A := s.gpr dst + BitVec.ofNat 32 (16 * k)) (by rw [u₁.gpr]; exact hi.ptr dst (by simp))
    (by rw [u₁.wr, hi.wr, addr_add]; exact hwr k hk) fun s₂ u₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ _ hz => WP.block_nil ?_
  have g₂ : ∀ r, s₂.gpr r = t.gpr r := fun r => by rw [u₂.gpr, u₁.gpr]
  have hcx : s₄.gpr .ecx = BitVec.ofNat 32 (m - k) := by
    rw [u₄.other _ (Ne.symm h3), u₃.other _ (Ne.symm h2), g₂, hi.cnt]
  have e16 : ∀ x : BitVec 32, x + BitVec.ofNat 32 (16 * k) + 16 = x + BitVec.ofNat 32 (16 * (k + 1)) := fun x => by
    rw [BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add, ← Nat.mul_succ]
  refine ⟨by rw [u₅.gpr, hcx], by rw [hz, hcx], fun r hr => ?_, fun r hr1 hr2 => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [u₅.other _ h2, u₄.other _ h1, u₃.gpr, g₂, hi.ptr _ (by simp), e16]
    · rw [u₅.other _ h3, u₄.gpr, u₃.other _ (Ne.symm h1), g₂, hi.ptr _ (by simp), e16]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr2
    rw [u₅.other _ hr1, u₄.other _ hr2.2, u₃.other _ hr2.1, g₂, hi.other _ hr1 (by simp [hr2])]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.xmm, u₁.mem, addr_zero, ptr_lt hD hk]
    conv => lhs; rw [show t.mem.writeW = (patch s.mem ((s.gpr dst).setWidth 64) (16 * k) _).writeW from
      congrArg Mem.writeW hi.mem]
    exact patch_write (by omega_using [hD, hk]) fun i hi16 => src_bytes hi hA (.inr hsd) hi16
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]

/-- XORing `m` blocks at `esi` with those at `edx`, to `ebx`, which is `edx` or apart. -/
theorem xor_loop {s : State} {m : Nat}
    (hm : m < 2 ^ 32) (h0 : 0 < m) (hc : s.gpr .ecx = BitVec.ofNat 32 m)
    (hA : (s.gpr .esi).toNat + 16 * m ≤ 2 ^ 32) (hS : (s.gpr .edx).toNat + 16 * m ≤ 2 ^ 32)
    (hD : (s.gpr .ebx).toNat + 16 * m ≤ 2 ^ 32)
    (hrA : BlocksIn (s.rd ++ s.wr) (s.gpr .esi) m) (hrS : BlocksIn (s.rd ++ s.wr) (s.gpr .edx) m)
    (hwr : BlocksIn s.wr (s.gpr .ebx) m)
    (hA' : Region.Disjoint ⟨(s.gpr .esi).setWidth 64, 16 * m⟩ ⟨(s.gpr .ebx).setWidth 64, 16 * m⟩)
    (hS' : s.gpr .edx = s.gpr .ebx ∨
      Region.Disjoint ⟨(s.gpr .edx).setWidth 64, 16 * m⟩ ⟨(s.gpr .ebx).setWidth 64, 16 * m⟩) :
    WP isa (.loop (.block xorBody) .ne) s
      (LDone s m .ebx (fun i => s.mem ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 i) ^^^
        s.mem ((s.gpr .edx).setWidth 64 + BitVec.ofNat 64 i)) [.esi, .edx, .ebx]) := by
  refine loop_ok hm h0 hc fun k t hi => ?_
  have hk := hi.hk
  refine wp_ldx (hi.ptr .esi (by decide)) (by rw [hi.rd, hi.wr, addr_add]; exact hrA k hk) fun s₁ u₁ => ?_
  refine wp_ldx (A := s.gpr .edx + BitVec.ofNat 32 (16 * k)) (by rw [u₁.gpr]; exact hi.ptr .edx (by decide))
    (by rw [u₁.rd, u₁.wr, hi.rd, hi.wr, addr_add]; exact hrS k hk) fun s₂ u₂ => ?_
  refine wp_pxor fun s₃ u₃ => ?_
  refine wp_stx (A := s.gpr .ebx + BitVec.ofNat 32 (16 * k)) (by rw [u₃.gpr, u₂.gpr, u₁.gpr]; exact hi.ptr .ebx (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr, hi.wr, addr_add]; exact hwr k hk) fun s₄ u₄ => ?_
  refine wp_addi fun s₅ u₅ => wp_addi fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_subi fun s₈ u₈ _ hz => WP.block_nil ?_
  have g₄ : ∀ r, s₄.gpr r = t.gpr r := fun r => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
  have hcx : s₇.gpr .ecx = BitVec.ofNat 32 (m - k) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), g₄, hi.cnt]
  have e16 : ∀ x : BitVec 32, x + BitVec.ofNat 32 (16 * k) + 16 = x + BitVec.ofNat 32 (16 * (k + 1)) := fun x => by
    rw [BitVec.add_assoc, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add, ← Nat.mul_succ]
  refine ⟨by rw [u₈.gpr, hcx], by rw [hz, hcx], fun r hr => ?_, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄,
        hi.ptr _ (by decide), e16]
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄,
        hi.ptr _ (by decide), e16]
    · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄,
        hi.ptr _ (by decide), e16]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h2
    rw [u₈.other _ h1, u₇.other _ h2.2.2, u₆.other _ h2.2.1, u₅.other _ h2.1, g₄, hi.other _ h1 (by simp [h2])]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.xmm, u₂.xmm, u₂.other .xmm0 (by decide), u₁.xmm, u₃.mem, u₂.mem,
      u₁.mem, addr_zero, ptr_lt hD hk]
    conv => lhs; rw [show t.mem.writeW = (patch s.mem ((s.gpr .ebx).setWidth 64) (16 * k) _).writeW from
      congrArg Mem.writeW hi.mem]
    refine patch_write (by omega_using [hD, hk]) fun i hi16 => ?_
    rw [BitVec.extractLsb'_xor, src_bytes hi hA (.inr hA') hi16, src_bytes hi hS hS' hi16]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]

/-! ## Blocks in the slots -/

/-- The bytes of the slots, as `InRel` has them. -/
theorem inRel_of_bytes {s : State} {B : BitVec 32} (hb : s.gpr .edi = B) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    {T : Nat → Spec.Aes.State}
    (h : ∀ i < 128, s.mem (B.setWidth 64 + BitVec.ofNat 64 i) = (T (i / 16)).getD (i % 16) 0) : InRel (Q s) T := by
  intro b hb8 i hi j hj
  have := h (16 * b + i) (by omega_using [hb8, hi])
  rw [show (16 * b + i) / 16 = b by omega_using [hi], show (16 * b + i) % 16 = i by omega_using [hi]] at this
  rw [← this]
  have e := byte_of_readW s.mem (addr B (16 * b)) hi
  rw [addr_eq (by omega_using [hfit, hb8]), BitVec.add_assoc, ← BitVec.ofNat_add] at e
  rw [← e, BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and]
  simp only [Q, StraightSse.xAddr]
  rw [show s.gpr sb = B from hb, addr_eq (by omega_using [hfit, hb8])]

theorem bytes_of_inRel {s : State} {B : BitVec 32} (hb : s.gpr .edi = B) (hfit : B.toNat + 2048 ≤ 2 ^ 32)
    {T : Nat → Spec.Aes.State} (h : InRel (Q s) T) :
    ∀ i < 128, s.mem (B.setWidth 64 + BitVec.ofNat 64 i) = (T (i / 16)).getD (i % 16) 0 := by
  intro i hi
  have hb8 : i / 16 < 8 := by omega_using [hi]
  have hi16 : i % 16 < 16 := Nat.mod_lt _ (by decide)
  have e := byte_of_readW s.mem (addr B (16 * (i / 16))) hi16
  rw [addr_eq (by omega_using [hfit, hb8]), BitVec.add_assoc, ← BitVec.ofNat_add, Nat.div_add_mod] at e
  rw [← e]
  refine byte_ext fun j hj => ?_
  have := h (i / 16) hb8 (i % 16) hi16 j hj
  simp only [Q, StraightSse.xAddr] at this
  rw [show s.gpr sb = B from hb, addr_eq (by omega_using [hfit, hb8])] at this
  rw [BitVec.getLsbD_extractLsb', decide_eq_true hj, Bool.true_and, this]

end VG.Proof.Aes.X86.Sse
