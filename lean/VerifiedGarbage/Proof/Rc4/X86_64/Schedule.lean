module

public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
import VerifiedGarbage.Proof.Rc4.X86_64.Lookup
public import VerifiedGarbage.Impl.Rc4.X86_64
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Rc4.Qword
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rc4.Memory

/-! ### `Rc4.X86_64.Replace`, which this module and modules that import it used -/

section

/-! # RC4 on x86-64: replacing a secret-indexed byte of the table -/

@[expose] public section

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-! ## Moving the difference to the byte's lane -/

/-- The difference `c`, once lanes `7, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 64 :=
  if jj ≤ L then (c.setWidth 64) <<< (8 * (L - jj)) else 0

theorem zero_xor' (x : BitVec 64) : (0 : BitVec 64) ^^^ x = x := BitVec.zero_xor
theorem or_zero' (x : BitVec 64) : x ||| (0 : BitVec 64) = x := BitVec.or_zero
theorem zero_or' (x : BitVec 64) : (0 : BitVec 64) ||| x = x := BitVec.zero_or
theorem rot_zero : (0 : BitVec 64).rotateRight 56 = 0 := by decide

theorem spread_succ (c : Byte) {L j : Nat} (hL : L < 8) :
    (spread c L (j + 1)).rotateRight 56 ||| (if L = j then c.setWidth 64 else 0) =
      spread c L j := by
  unfold spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, rot_byte c (by omega_using [hL]), ite_eq_right (show ¬ L = j by omega_using [h1]),
      or_zero', ite_eq_left (show j ≤ L by omega_using [h1]), show L - (j + 1) + 1 = L - j by omega_using [h1]]
  · rw [ite_eq_right h1, rot_zero, zero_or']
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega_using [h2]), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega_using [h1, h2])]

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 8)
    (h9 : s.gpr .r9 = idx.setWidth 64) (hax : s.gpr .rax = c.setWidth 64)
    (h11 : s.gpr .r11 = spread c (idx.toNat % 8) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .r11 = spread c (idx.toNat % 8) j ∧ t.gpr .rax = s.gpr .rax ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.mem = s.mem := by
  unfold spreadStep laneMask
  rrun [h9, hax, h11, sx j (by omega_using [hj]), sx 56]
  rw [lane_mask idx hj, spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (hax : s₀.gpr .rax = c.setWidth 64) :
    ∀ n ≤ 8, ∀ s, s.gpr .r11 = spread c (idx.toNat % 8) n → s.gpr .rax = s₀.gpr .rax →
      s.gpr .r9 = s₀.gpr .r9 → s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .r11 = spread c (idx.toNat % 8) 0 ∧ t.gpr .rax = s₀.gpr .rax ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s h11 hax' _ hm; exact WP.block_nil ⟨h11, hax', hm⟩
  | succ n ih =>
    intro s h11 hax' h9' hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (spread_step s idx c (by omega_using [hn]) (h9'.trans h9) (hax'.trans hax) h11)
      fun t ⟨t11, tax, t9, tm⟩ => ?_
    exact ih (by omega_using [hn]) t t11 (tax.trans hax') (t9.trans h9') (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 8).reverse := rfl

/-! ## Storing back every quadword -/

/-- The memory once quadwords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) : Mem :=
  if n / 8 < k then
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) :
    (scatter m p n d k).writeW (p + BitVec.ofNat 64 (8 * k))
      ((if n / 8 = k then d else 0) ^^^
        (scatter m p n d k).readW (p + BitVec.ofNat 64 (8 * k)) 64) = scatter m p n d (k + 1) := by
  unfold scatter
  by_cases h0 : n / 8 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 8 = k by omega_using [h0]), zero_xor', writeW_readW,
      ite_eq_left (show n / 8 < k + 1 by omega_using [h0])]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 8 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 8 < k + 1 by omega_using [h1]), BitVec.xor_comm, h1]
    · rw [ite_eq_right h1, zero_xor', writeW_readW,
        ite_eq_right (show ¬ n / 8 < k + 1 by omega_using [h0, h1])]

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h9 : s.gpr .r9 = idx.setWidth 64)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 (8 * k))
        ((if idx.toNat / 8 = k then s.gpr .r11 else 0) ^^^
          s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 64) ∧
      t.gpr .r11 = s.gpr .r11 ∧ t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scatterStep rowMask
  rrun [h9, hr, hw, sx (8 * k) (by omega_using [hk])]
  rw [row_mask idx hk]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 64)
    (h9 : s₀.gpr .r9 = idx.setWidth 64) (hw : InRegions s₀.wr (s₀.gpr .rdi) 256) :
    ∀ n ≤ 32, ∀ s, s.gpr .r11 = d → s.gpr .r9 = s₀.gpr .r9 → s.gpr .rdi = s₀.gpr .rdi →
      s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (s₀.gpr .rdi) idx.toNat d n ∧ t.gpr .r11 = d ∧
        t.gpr .r9 = s₀.gpr .r9 ∧ t.gpr .rdi = s₀.gpr .rdi ∧ t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s h11 h9' hdi hwr hm
    refine WP.block_nil ⟨?_, h11, h9', hdi, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h11 h9' hdi hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn]) s h11 h9' hdi hwr hm) fun t ⟨tm, t11, t9, tdi, twr⟩ => ?_
    have hq : InRegions t.wr (t.gpr .rdi + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [twr, tdi]
      exact region_offset _ _ _ _ _ (by omega_using [hn]) (by omega_using [hn]) hw
    refine WP.mono (scatter_step t idx (by omega_using [hn]) (t9.trans h9) hq)
      fun u ⟨um, u11, u9, udi, _, uwr⟩ => ?_
    refine ⟨?_, u11.trans t11, u9.trans t9, udi.trans tdi, uwr.trans twr⟩
    rw [um, tm, t11, tdi, scatter_succ]

/-! ## The replacement -/

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem replace_core (s : State) (idx ii : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (hcx : s.gpr .rcx = ii.setWidth 64) (hw : InRegions s.wr (s.gpr .rdi) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .rax = (s.mem (s.gpr .rdi + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 :=
    region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hr
  let p := s.gpr .rdi
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r10, .r11] (lookup_core s idx h9 hr) (by decide +kernel))
    fun t ⟨⟨tax, tm⟩, tk⟩ => ?_
  have t9 : t.gpr .r9 = s.gpr .r9 := tk.gpr (by decide)
  have tdi : t.gpr .rdi = s.gpr .rdi := tk.gpr (by decide)
  have tcx : t.gpr .rcx = s.gpr .rcx := tk.gpr (by decide)
  have hit : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rcx) 1 := by
    rw [hcx, byte_addr]; exact hi
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.movzx8 .r11 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r11),
      .mov .r11 (imm 0)]) t fun u =>
      u.gpr .rax = (b ^^^ v).setWidth 64 ∧ u.gpr .r11 = 0 ∧ u.gpr .r9 = s.gpr .r9 ∧
        u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rcx = s.gpr .rcx ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
        u.wr = s.wr := by
    rrun [hit, tax, tm, t9, tdi, tcx, tk.2.1, tk.2.2]
    rw [hcx, byte_addr ii, xor_byte]
  refine WP.mono h1 fun u ⟨uax, u11, u9, udi, ucx, um, urd, uwr⟩ => ?_
  rw [WP.block_append_iff]
  have hsp := spread_steps u idx (b ^^^ v) (u9.trans h9) uax 8 (by decide) u
    (by rw [u11]; unfold spread; rw [ite_eq_right (by omega_using [])]) rfl rfl rfl
  rw [← lanesDown_eq] at hsp
  refine WP.mono (WP.keep [.r10, .r11] hsp (by decide +kernel)) fun w ⟨⟨w11, wax, wm⟩, wk⟩ => ?_
  have w9 : w.gpr .r9 = s.gpr .r9 := (wk.gpr (by decide)).trans u9
  have wdi : w.gpr .rdi = s.gpr .rdi := (wk.gpr (by decide)).trans udi
  have wcx : w.gpr .rcx = s.gpr .rcx := (wk.gpr (by decide)).trans ucx
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  have hiw : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rcx) 1 := by
    rw [hcx, byte_addr]; exact hi
  rw [WP.block_append_iff]
  have h2 : WP isa (.block [.movzx8 .r10 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r10)]) w
      fun x => x.gpr .rax = b.setWidth 64 ∧ x.gpr .r11 = w.gpr .r11 ∧ x.gpr .r9 = s.gpr .r9 ∧
        x.gpr .rdi = s.gpr .rdi ∧ x.mem = s.mem ∧ x.wr = s.wr := by
    rrun [hiw, wax, uax, wm, um, w9, wdi, wcx, wwr, wrd]
    rw [hcx, byte_addr ii, xor_byte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, x11, x9, xdi, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.r10] (scatter_steps s idx _ h9 hw 32 (by decide) x rfl x9 xdi xwr xm)
    (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, x11, w11]
  unfold scatter spread
  rw [ite_eq_left (by omega_using []), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.X86_64

end

end

/-! # RC4 on x86-64: key scheduling -/

@[expose] public section

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

theorem writeW_byte8 (m : Mem) (a : Addr) (v : Byte) : m.writeW a v = m.write a 1 v := by
  change m.write a 1 (v.setWidth 8) = _
  rw [BitVec.setWidth_eq]

theorem low_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low (r : Nat) : (BitVec.ofNat 64 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem mask255 (x : BitVec 64) : x &&& BitVec.ofNat 64 255 = (x.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem byte_add (a b : Byte) :
    a.setWidth 64 + b.setWidth 64 &&& BitVec.ofNat 64 255 = (a + b).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_using []

theorem byte_add3 (j a k : Byte) :
    j.setWidth 64 + a.setWidth 64 + k.setWidth 64 &&& BitVec.ofNat 64 255 =
      (j + a + k).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_using []

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (s₀.gpr .rdi) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .rdi = s₀.gpr .rdi ∧ s.gpr .rsi = s₀.gpr .rsi ∧ s.gpr .rdx = s₀.gpr .rdx ∧
    s.gpr .rcx = BitVec.ofNat 64 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 == 0#64) := by
  obtain ⟨hm, hrd, hwr, hdi, hsi, hdx, hcx⟩ := h
  have hw : InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hp
  have hadd : BitVec.ofNat 64 r + BitVec.ofNat 64 1 = BitVec.ofNat 64 (r + 1) := by
    rw [← BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hdi, hsi, hdx, hcx, hadd, writeW_byte8, ofNat_low, IdentityInv]
  exact ⟨identityMem_store _ _ _ hr, rfl⟩

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) .ne) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 ≠ 0#64 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rsi + s.gpr .r8) 1) :
    WP isa (.block [.movzx8 .r10 (atIdx .rdi .rcx), .alu .add .r9 (.reg .r10),
      .movzx8 .r10 (atIdx .rsi .r8), .alu .add .r9 (.reg .r10), .alu .and .r9 (imm 255)]) s
      fun t => t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 i.toNat) +
          s.mem (s.gpr .rsi + s.gpr .r8)).setWidth 64 ∧ Keep [.r9, .r10] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + i.setWidth 64) 1 := by
    rw [byte_addr i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .r9 = (j + s.mem (s.gpr .rdi + BitVec.ofNat 64 i.toNat) +
      s.mem (s.gpr .rsi + s.gpr .r8)).setWidth 64 ∧ t.mem = s.mem) [.r9, .r10] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  rrun [hi, hk, h9, hcx]
  rw [byte_addr i, byte_add3]

theorem and_mask (x : BitVec 64) (p : Bool) :
    x &&& (0#64 - (BitVec.ofBool p).setWidth 64) = if p then x else 0 := by
  rw [borrow_mask]
  cases p
  · exact BitVec.and_zero
  · exact BitVec.and_allOnes

theorem schedule_after (s : State) (i b : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (hax : s.gpr .rax = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1) :
    WP isa (.block [.store8 (atIdx .rdi .rcx) .rax,
      .alu .add .r8 (imm 1), .mov .r10 (imm 0), .alu .cmp .r8 (.reg .rdx),
      .alu .sbb .r10 (.reg .r10),
      .alu .and .r8 (.reg .r10),
      .alu .add .rcx (imm 1), .alu .cmp .rcx (imm 256)]) s fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r8 = (if (s.gpr .r8 + 1#64).toNat < (s.gpr .rdx).toNat then s.gpr .r8 + 1#64
        else 0#64) ∧
      t.gpr .rcx = i.setWidth 64 + 1#64 ∧
      t.zf = some (i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 == 0#64) ∧
      Keep [.rcx, .r8, .r10] s t := by
  have hw' : InRegions s.wr (s.gpr .rdi + i.setWidth 64) 1 := by rw [byte_addr i]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r8 = (if (s.gpr .r8 + 1#64).toNat < (s.gpr .rdx).toNat then s.gpr .r8 + 1#64
        else 0#64) ∧
      t.gpr .rcx = i.setWidth 64 + 1#64 ∧
      t.zf = some (i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 == 0#64)) [.rcx, .r8, .r10] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hw', hcx, hax, writeW_byte8, low_byte, and_mask]
  refine ⟨by rw [byte_addr i], ?_, rfl⟩
  simp only [decide_eq_true_eq]
  rfl

/-- One concrete key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte)
    (hcx : s.gpr .rcx = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .rdi) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .rsi + s.gpr .r8) 1) :
    let a := s.mem (s.gpr .rdi + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (s.gpr .rsi + s.gpr .r8)
    let b := s.mem (s.gpr .rdi + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (s.gpr .rdi + BitVec.ofNat 64 jj.toNat) 1 a).write
        (s.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r8 = (if (s.gpr .r8 + 1#64).toNat < (s.gpr .rdx).toNat then s.gpr .r8 + 1#64
        else 0#64) ∧
      t.gpr .r9 = jj.setWidth 64 ∧ t.gpr .rcx = i.setWidth 64 + 1#64 ∧
      t.zf = some (i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 == 0#64) ∧
      Keep ([.r9, .r10] ++ [.rax, .r10, .r11] ++ [.rcx, .r8, .r10]) s t := by
  intro a jj b
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j hcx h9 hr hk) fun t ⟨t9, tk, tm⟩ => ?_
  have tcx : t.gpr .rcx = i.setWidth 64 := (tk.gpr (by decide)).trans hcx
  have tdi : t.gpr .rdi = s.gpr .rdi := tk.gpr (by decide)
  have tr8 : t.gpr .r8 = s.gpr .r8 := tk.gpr (by decide)
  have tdx : t.gpr .rdx = s.gpr .rdx := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .rdi) 256 := by rw [tk.2.2, tdi]; exact hp
  refine WP.mono (WP.keep [.rax, .r10, .r11] (replace_core t jj i t9 tcx htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have ucx : u.gpr .rcx = i.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have udi : u.gpr .rdi = s.gpr .rdi := (uk.gpr (by decide)).trans tdi
  have ur8 : u.gpr .r8 = s.gpr .r8 := (uk.gpr (by decide)).trans tr8
  have udx : u.gpr .rdx = s.gpr .rdx := (uk.gpr (by decide)).trans tdx
  have u9 : u.gpr .r9 = jj.setWidth 64 := (uk.gpr (by decide)).trans t9
  rw [tm, tdi] at uax um
  have hw : InRegions u.wr (u.gpr .rdi + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, udi]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) hp
  refine WP.mono (schedule_after u i b ucx uax hw) fun v ⟨vm, v8, vcx, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans u9, vcx, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, udi]
  · rw [v8, ur8, udx]

/-- The key bytes, from the key pointer and length of a state. -/
def keyAt (s : State) : List Byte := bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat

structure ScheduleInv (s₀ : State) (r : Nat) (s : State) : Prop where
  frame : TableFrame (s₀.gpr .rdi) s₀.mem s.mem
  table : (contextAt s.mem (s₀.gpr .rdi)).table = (schedulePrefix (keyAt s₀) r).1
  j : s.gpr .r9 = (schedulePrefix (keyAt s₀) r).2.setWidth 64
  i : s.gpr .rcx = BitVec.ofNat 64 r
  off : s.gpr .r8 = BitVec.ofNat 64 (r % (s₀.gpr .rdx).toNat)
  p : s.gpr .rdi = s₀.gpr .rdi
  len : s.gpr .rdx = s₀.gpr .rdx
  key : s.gpr .rsi = s₀.gpr .rsi
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem schedule_inv_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .rdx).toNat ∧ (s₀.gpr .rdx).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi) (s₀.gpr .rdx).toNat)
    (hs : Mem.Sep (s₀.gpr .rsi) (s₀.gpr .rdx).toNat (s₀.gpr .rdi) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ (r + 1) t ∧
      t.zf = some (BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 == 0#64) := by
  let key := keyAt s₀
  let st := schedulePrefix key r
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .rcx = (BitVec.ofNat 8 r).setWidth 64 := by
    rw [h.i, byte_addr, hrt]
  have hpoint : InRegions s.wr (s.gpr .rdi) 256 := by rw [h.wr, h.p]; exact hp
  have hmod := Nat.mod_lt r (show 0 < (s₀.gpr .rdx).toNat by omega_using [hlen])
  have hkeypoint : InRegions (s.rd ++ s.wr) (s.gpr .rsi + s.gpr .r8) 1 := by
    rw [h.rd, h.wr, h.key, h.off]
    exact region_offset _ _ _ _ _ (by omega_using [hmod]) (by omega_using [hmod]) hk
  have hkeybyte : s.mem (s.gpr .rsi + s.gpr .r8) = key.getD (r % key.length) 0 := by
    rw [h.key, h.off]
    have hsep := hs (s₀.gpr .rsi + BitVec.ofNat 64 (r % (s₀.gpr .rdx).toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hmod])]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyAt]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (s.gpr .rdi + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem (s₀.gpr .rdi) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ hi h.j hpoint hkeypoint) fun t ⟨tm, t8, t9, tcx, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 64 + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [byte_addr, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.len,
    (tk.gpr (by decide)).trans h.key, tk.2.1.trans h.rd, tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [t9, hrt, htablebyte, hkeybyte, hnext]
  · rw [tcx, hcast]
  · rw [t8, h.off, h.len]
    exact key_next r _ (by omega_using [hlen]) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .rdx).toNat ∧ (s₀.gpr .rdx).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .rdi) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rsi) (s₀.gpr .rdx).toNat)
    (hs : Mem.Sep (s₀.gpr .rsi) (s₀.gpr .rdx).toNat (s₀.gpr .rdi) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.loop (.block scheduleStep) .ne) s (ScheduleInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t hj hlen hp hk hs ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 ≠ 0#64 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

end VG.Proof.Rc4.X86_64
