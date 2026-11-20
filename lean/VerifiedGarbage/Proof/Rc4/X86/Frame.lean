module

import VerifiedGarbage.Proof.Rc4.X86.ConstantTime
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Rc4.Dword
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Impl.Rc4.X86
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
public import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.Proof.Rc4.X86.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Rc4.X86.Lit
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule

/-! ### `Rc4.X86.Schedule`, which only this module used -/

section

/-! # RC4 on x86 (32-bit): key scheduling -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

theorem and_mask32 (x : BitVec 32) (p : Bool) :
    x &&& (0#32 - (BitVec.ofBool p).setWidth 32) = if p then x else 0 := by
  rw [borrow_mask32]
  cases p
  · exact BitVec.and_zero
  · exact BitVec.and_allOnes

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem ((s₀.gpr .edi).setWidth 64) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .edi = s₀.gpr .edi ∧ s.gpr .esp = s₀.gpr .esp ∧ s.gpr .esi = BitVec.ofNat 32 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.zf = some (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  obtain ⟨hm, hrd, hwr, hdi, hsp, hsi⟩ := h
  have he : addr (s₀.gpr .edi + BitVec.ofNat 32 r) 0 =
      (s₀.gpr .edi).setWidth 64 + BitVec.ofNat 64 r := by
    have := idx_addr hfit (BitVec.ofNat 8 r)
    rwa [byte32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr] at this
  have hw : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64 + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega_arith) (by omega_arith) hp
  have hadd : BitVec.ofNat 32 r + BitVec.ofNat 32 1 = BitVec.ofNat 32 (r + 1) := by
    rw [← BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hdi, hsp, hsi, hadd, writeW_byte8, ofNat_low32, IdentityInv, he]
  exact ⟨identityMem_store _ _ _ hr, rfl⟩

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) .ne) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hfit hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega_arith, j + 1, by omega_arith, rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte) (K : BitVec 32)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256)
    (hka : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hkv : s.mem.readW (addr (s.gpr .esp) 4) 32 = K)
    (hk : InRegions (s.rd ++ s.wr) (addr (K + s.gpr .ebx) 0) 1) :
    WP isa (.block (loadI ++ ([.alu .add .ebp (.reg .edx), .mov .edx (.mem (at_ .esp 4)),
      .alu .add .edx (.reg .ebx), .movzx8 .edx (at_ .edx 0), .alu .add .ebp (.reg .edx),
      .alu .and .ebp (imm 255)] : List Instr))) s
      fun t => t.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) +
          s.mem (addr (K + s.gpr .ebx) 0)).setWidth 32 ∧ Keep [.ebp, .edx] s t ∧ t.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok s i hsi hfit hp) fun t ⟨tdx, tk, tm⟩ => ?_
  have tbp : t.gpr .ebp = j.setWidth 32 := (tk.gpr (by decide)).trans hbp
  have tbx : t.gpr .ebx = s.gpr .ebx := tk.gpr (by decide)
  have tsp : t.gpr .esp = s.gpr .esp := tk.gpr (by decide)
  refine WP.mono (WP.keep (Q := fun u => u.gpr .ebp = (j + s.mem ((s.gpr .edi).setWidth 64 +
      BitVec.ofNat 64 i.toNat) + s.mem (addr (K + s.gpr .ebx) 0)).setWidth 32 ∧ u.mem = s.mem)
      [.ebp, .edx] ?_ (by decide +kernel)) fun u ⟨h, hk'⟩ => ⟨h.1, ?_, h.2⟩
  · rrun [tbp, tdx, tsp, tbx, tm, tk.2.1, tk.2.2, hka, hkv, hk]
    rw [byte_add3_32]
  · exact (tk.trans hk').mono (by decide)

theorem schedule_after (s : State) (i b : Byte) (Lk : BitVec 32)
    (hsi : s.gpr .esi = i.setWidth 32) (hax : s.gpr .eax = b.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1)
    (hla : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hlv : s.mem.readW (addr (s.gpr .esp) 8) 32 = Lk) :
    WP isa (.block [.alu .add .ebx (imm 1), .mov .edx (.mem (at_ .esp 8)),
      .alu .cmp .ebx (.reg .edx), .mov .edx (imm 0), .alu .sbb .edx (.reg .edx),
      .alu .and .ebx (.reg .edx), .mov .edx (.reg .edi), .alu .add .edx (.reg .esi),
      .store8 (at_ .edx 0) .al, .alu .add .esi (imm 1), .alu .cmp .esi (imm 256)]) s fun t =>
      t.mem = s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .ebx = (if (s.gpr .ebx + 1#32).toNat < Lk.toNat then s.gpr .ebx + 1#32 else 0#32) ∧
      t.gpr .esi = i.setWidth 32 + 1#32 ∧
      t.zf = some (i.setWidth 32 + 1#32 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep [.ebx, .esi, .edx] s t := by
  have he := idx_addr hfit i
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .ebx = (if (s.gpr .ebx + 1#32).toNat < Lk.toNat then s.gpr .ebx + 1#32 else 0#32) ∧
      t.gpr .esi = i.setWidth 32 + 1#32 ∧
      t.zf = some (i.setWidth 32 + 1#32 - BitVec.ofNat 32 256 == 0#32)) [.ebx, .esi, .edx] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hsi, hax, he, hw, hla, hlv, writeW_byte8, low_byte32, and_mask32]
  refine ⟨?_, rfl⟩
  simp only [decide_eq_true_eq]
  rfl

/-- One concrete key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte) (K Lk : BitVec 32)
    (hsi : s.gpr .esi = i.setWidth 32) (hbp : s.gpr .ebp = j.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hp : InRegions s.wr ((s.gpr .edi).setWidth 64) 256)
    (hka : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hkv : s.mem.readW (addr (s.gpr .esp) 4) 32 = K)
    (hla : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    (hlv : s.mem.readW (addr (s.gpr .esp) 8) 32 = Lk)
    (hk : InRegions (s.rd ++ s.wr) (addr (K + s.gpr .ebx) 0) 1)
    (hsl : Mem.Sep (addr (s.gpr .esp) 8) 4 ((s.gpr .edi).setWidth 64) 256) :
    let p := (s.gpr .edi).setWidth 64
    let a := s.mem (p + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (addr (K + s.gpr .ebx) 0)
    let b := s.mem (p + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (p + BitVec.ofNat 64 jj.toNat) 1 a).write
        (p + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .ebx = (if (s.gpr .ebx + 1#32).toNat < Lk.toNat then s.gpr .ebx + 1#32 else 0#32) ∧
      t.gpr .ebp = jj.setWidth 32 ∧ t.gpr .esi = i.setWidth 32 + 1#32 ∧
      t.zf = some (i.setWidth 32 + 1#32 - BitVec.ofNat 32 256 == 0#32) ∧
      Keep ([.ebp, .edx] ++ [.eax, .ecx, .edx] ++ [.ebx, .esi, .edx]) s t := by
  intro p a jj b
  have hr : InRegions (s.rd ++ s.wr) p 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j K hsi hbp hfit hr hka hkv hk) fun t ⟨tbp, tk, tm⟩ => ?_
  have tsi : t.gpr .esi = i.setWidth 32 := (tk.gpr (by decide)).trans hsi
  have tdi : t.gpr .edi = s.gpr .edi := tk.gpr (by decide)
  have tbx : t.gpr .ebx = s.gpr .ebx := tk.gpr (by decide)
  have tsp : t.gpr .esp = s.gpr .esp := tk.gpr (by decide)
  have htp : InRegions t.wr ((t.gpr .edi).setWidth 64) 256 := by rw [tk.2.2, tdi]; exact hp
  refine WP.mono (WP.keep [.eax, .ecx, .edx]
    (replace_core t jj i tbp tsi (by rw [tdi]; exact hfit) htp) (by decide +kernel))
    fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have usi : u.gpr .esi = i.setWidth 32 := (uk.gpr (by decide)).trans tsi
  have udi : u.gpr .edi = s.gpr .edi := (uk.gpr (by decide)).trans tdi
  have ubx : u.gpr .ebx = s.gpr .ebx := (uk.gpr (by decide)).trans tbx
  have usp : u.gpr .esp = s.gpr .esp := (uk.gpr (by decide)).trans tsp
  have ubp : u.gpr .ebp = jj.setWidth 32 := (uk.gpr (by decide)).trans tbp
  rw [tm, tdi] at uax um
  have hw : InRegions u.wr ((u.gpr .edi).setWidth 64 + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, udi]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_arith) (by have := i.isLt; omega_arith) hp
  have hla' : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 8) 4 := by
    rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2, usp]; exact hla
  have hlv' : u.mem.readW (addr (u.gpr .esp) 8) 32 = Lk := by
    rw [um, usp, ← hlv]
    simp only [Mem.readW, Nat.reduceDiv]
    rw [Mem.read_write_sep (sep_offset_right hsl (by have := jj.isLt; omega_arith)
      (by have := jj.isLt; omega_arith)) (by decide)]
  refine WP.mono (schedule_after u i b Lk usi uax (by rw [udi]; exact hfit) hw hla' hlv')
    fun v ⟨vm, vbx, vsi, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans ubp, vsi, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, udi]
  · rw [vbx, ubx]

/-- The key bytes, at `K` (32-bit), `Lk` of them. -/
def keyOf (m : Mem) (K Lk : BitVec 32) : List Byte := bytesAt m (K.setWidth 64) Lk.toNat

structure ScheduleInv (s₀ : State) (K Lk : BitVec 32) (r : Nat) (s : State) : Prop where
  frame : TableFrame ((s₀.gpr .edi).setWidth 64) s₀.mem s.mem
  table : (contextAt s.mem ((s₀.gpr .edi).setWidth 64)).table =
    (schedulePrefix (keyOf s₀.mem K Lk) r).1
  j : s.gpr .ebp = (schedulePrefix (keyOf s₀.mem K Lk) r).2.setWidth 32
  i : s.gpr .esi = BitVec.ofNat 32 r
  off : s.gpr .ebx = BitVec.ofNat 32 (r % Lk.toNat)
  p : s.gpr .edi = s₀.gpr .edi
  sp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What key scheduling needs of the state it starts from. -/
structure SchedulePre (s₀ : State) (K Lk : BitVec 32) : Prop where
  len : 1 ≤ Lk.toNat ∧ Lk.toNat ≤ 256
  fit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32
  table : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256
  key : InRegions (s₀.rd ++ s₀.wr) (K.setWidth 64) Lk.toNat
  keyFit : K.toNat + Lk.toNat ≤ 2 ^ 32
  keySep : Mem.Sep (K.setWidth 64) Lk.toNat ((s₀.gpr .edi).setWidth 64) 256
  ka : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 4) 4
  kv : s₀.mem.readW (addr (s₀.gpr .esp) 4) 32 = K
  la : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) 8) 4
  lv : s₀.mem.readW (addr (s₀.gpr .esp) 8) 32 = Lk
  ks : Mem.Sep (addr (s₀.gpr .esp) 4) 4 ((s₀.gpr .edi).setWidth 64) 256
  ls : Mem.Sep (addr (s₀.gpr .esp) 8) 4 ((s₀.gpr .edi).setWidth 64) 256

theorem key_addr {K : BitVec 32} {Lk : BitVec 32} (hfit : K.toNat + Lk.toNat ≤ 2 ^ 32) {o : Nat}
    (ho : o < Lk.toNat) : addr (K + BitVec.ofNat 32 o) 0 = K.setWidth 64 + BitVec.ofNat 64 o := by
  unfold addr
  rw [BitVec.add_zero]
  exact VG.Proof.MlKem.X86.ea_off (by omega_arith)

theorem schedule_inv_step (s₀ s : State) (K Lk : BitVec 32) {r : Nat} (hr : r < 256)
    (hpre : SchedulePre s₀ K Lk) (h : ScheduleInv s₀ K Lk r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ K Lk (r + 1) t ∧
      t.zf = some (BitVec.ofNat 32 (r + 1) - BitVec.ofNat 32 256 == 0#32) := by
  let key := keyOf s₀.mem K Lk
  let st := schedulePrefix key r
  have hlen := hpre.len
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .esi = (BitVec.ofNat 8 r).setWidth 32 := by
    rw [h.i, byte32, hrt]
  have hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [h.p]; exact hpre.fit
  have hpoint : InRegions s.wr ((s.gpr .edi).setWidth 64) 256 := by rw [h.wr, h.p]; exact hpre.table
  have hmod := Nat.mod_lt r (show 0 < Lk.toNat by omega_arith)
  have hka : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := by
    rw [h.rd, h.wr, h.sp]; exact hpre.ka
  have hla : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := by
    rw [h.rd, h.wr, h.sp]; exact hpre.la
  have hkv : s.mem.readW (addr (s.gpr .esp) 4) 32 = K := by
    rw [h.sp, table_frame_readW h.frame hpre.ks]; exact hpre.kv
  have hlv : s.mem.readW (addr (s.gpr .esp) 8) 32 = Lk := by
    rw [h.sp, table_frame_readW h.frame hpre.ls]; exact hpre.lv
  have hkaddr : addr (K + s.gpr .ebx) 0 = K.setWidth 64 + BitVec.ofNat 64 (r % Lk.toNat) := by
    rw [h.off]; exact key_addr hpre.keyFit hmod
  have hkeypoint : InRegions (s.rd ++ s.wr) (addr (K + s.gpr .ebx) 0) 1 := by
    rw [h.rd, h.wr, hkaddr]
    exact region_offset _ _ _ _ _ (by omega_arith) (by omega_arith) hpre.key
  have hkeybyte : s.mem (addr (K + s.gpr .ebx) 0) = key.getD (r % key.length) 0 := by
    rw [hkaddr]
    have hsep := hpre.keySep (K.setWidth 64 + BitVec.ofNat 64 (r % Lk.toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyOf]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem ((s₀.gpr .edi).setWidth 64) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  have hsl : Mem.Sep (addr (s.gpr .esp) 8) 4 ((s.gpr .edi).setWidth 64) 256 := by
    rw [h.sp, h.p]; exact hpre.ls
  refine WP.mono (schedule_step s _ _ K Lk hi h.j hfit hpoint hka hkv hla hlv hkeypoint hsl)
    fun t ⟨tm, tbx, tbp, tsi, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 32 + 1#32 = BitVec.ofNat 32 (r + 1) := by
    rw [byte32, hrt, ← BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.sp,
    tk.2.1.trans h.rd, tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [tbp, hrt, htablebyte, hkeybyte, hnext]
  · rw [tsi, hcast]
  · rw [tbx, h.off]
    exact key_next32 r _ (by omega_arith) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) (K Lk : BitVec 32) {r : Nat} (hr : r < 256)
    (hpre : SchedulePre s₀ K Lk) (h : ScheduleInv s₀ K Lk r s) :
    WP isa (.loop (.block scheduleStep) .ne) s (ScheduleInv s₀ K Lk 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ K Lk j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t K Lk hj hpre ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, hz, hend, Option.map_some]
    rfl
  · right
    have hnz : BitVec.ofNat 32 (j + 1) - BitVec.ofNat 32 256 ≠ 0#32 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega_arith, j + 1, by omega_arith, rfl, hu⟩
    simp only [eval, hz, Option.map_some, beq_eq_false_iff_ne.mpr hnz, Bool.not_false]

end VG.Proof.Rc4.X86

end

end

/-! ### `Rc4.X86.Verified`, which only this module used -/

section

/-! ### `Rc4.X86.Init`, which only this module used -/

section

/-! # RC4 on x86 (32-bit): checked initialization -/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- `vg_rc4_init(key, key_len, ctx, scratch)`: what its proof needs of the state on entry. -/
structure InitPre (s : State) : Prop where
  args : InRegions s.rd (argAddr s 0) 16
  key : InRegions s.rd ((arg s 0).setWidth 64) (arg s 1).toNat
  ctx : InRegions s.wr ((arg s 2).setWidth 64) 258
  scratch : InRegions s.wr ((arg s 3).setWidth 64) 64
  keyFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  ctxFit : (arg s 2).toNat + 258 ≤ 2 ^ 32
  scratchFit : (arg s 3).toNat + 64 ≤ 2 ^ 32
  spFit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  keyCtx : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 2).setWidth 64, 258⟩
  keyScratch : Region.Disjoint ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩ ⟨(arg s 3).setWidth 64, 64⟩
  ctxScratch : Region.Disjoint ⟨(arg s 2).setWidth 64, 258⟩ ⟨(arg s 3).setWidth 64, 64⟩
  argsCtx : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 2).setWidth 64, 258⟩
  argsScratch : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 64⟩

/-- Memory changed only within the context and `scratch`. -/
def InitFrame (s : State) (m : Mem) : Prop :=
  Frame [⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩] s.mem m

theorem InitPre.arg_off {s : State} (hp : InitPre s) (i : Nat) (hi : i < 4) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  unfold argAddr
  rw [VG.Proof.MlKem.X86.ea_off (by have := hp.spFit; omega_using [hi, this]),
    VG.Proof.MlKem.X86.ea_off (by have := hp.spFit; omega_using [this]), BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- An argument, read from memory changed only within the context and `scratch`. -/
theorem InitPre.arg_eq {s : State} (hp : InitPre s) {m : Mem} (hf : InitFrame s m) {i : Nat}
    (hi : i < 4) : m.readW (argAddr s i) 32 = arg s i := by
  refine hf.readW (r := ⟨argAddr s 0, 16⟩) ?_ ?_ (by decide)
  · rw [hp.arg_off i hi]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.argsCtx
    · exact hp.argsScratch

theorem InitPre.arg_in {s : State} (hp : InitPre s) {i : Nat} (hi : i < 4) :
    InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
  obtain h := region_offset _ _ _ (4 * i) 4 (by omega_using [hi]) (by omega_using [hi]) hp.args
  rw [← hp.arg_off i hi] at h
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem InitFrame.table {s : State} {m m' : Mem} (hf : InitFrame s m)
    (ht : TableFrame ((arg s 2).setWidth 64) m m') : InitFrame s m' := by
  intro x hx
  rw [ht x ?_, hf x hx]
  intro hlt
  apply hx ⟨(arg s 2).setWidth 64, 258⟩ List.mem_cons_self
  simp only [Region.Contains]
  omega_using [hlt]

theorem InitPre.arg_contains {s : State} (hp : InitPre s) {i : Nat} (hi : i < 4) :
    (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s i) 4 := by
  rw [hp.arg_off i hi]
  exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])

theorem InitPre.arg_sep {s : State} (hp : InitPre s) {i : Nat} (hi : i < 4) :
    Mem.Sep (argAddr s i) 4 ((arg s 2).setWidth 64) 256 := fun x h₁ h₂ =>
  hp.argsCtx x ((hp.arg_contains hi).byte h₁) (by simp only [Region.Contains]; omega_using [h₂])

theorem init_finish (s : State) (hfit : (s.gpr .edi).toNat + 258 ≤ 2 ^ 32)
    (hp : InRegions s.wr ((s.gpr .edi).setWidth 64) 258) :
    WP isa (.block [.mov .eax (imm 0), .store8 (at_ .edi 256) .al, .store8 (at_ .edi 257) .al]) s
      fun t => t.gpr .eax = 0#32 ∧
        t.mem = (s.mem.write ((s.gpr .edi).setWidth 64 + 256#64) 1 0#8).write
          ((s.gpr .edi).setWidth 64 + 257#64) 1 0#8 ∧ Keep [.eax] s t := by
  obtain h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  obtain h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  obtain a256 : addr (s.gpr .edi) 256 = (s.gpr .edi).setWidth 64 + 256#64 := addr_of_fit (by omega_using [hfit])
  obtain a257 : addr (s.gpr .edi) 257 = (s.gpr .edi).setWidth 64 + 257#64 := addr_of_fit (by omega_using [hfit])
  refine WP.mono (WP.keep (Q := fun t => t.gpr .eax = 0#32 ∧
      t.mem = (s.mem.write ((s.gpr .edi).setWidth 64 + 256#64) 1 0#8).write
        ((s.gpr .edi).setWidth 64 + 257#64) 1 0#8) [.eax] ?_ (by decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  rrun [a256, a257, h256, h257, writeW_byte8]
  exact rfl

theorem init_valid (s : State) (hp : InitPre s)
    (hlen : 1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256) :
    WP isa initValid s fun t => t.gpr .eax = 0#32 ∧
      contextAt t.mem ((arg s 2).setWidth 64) =
        { table := keySchedule (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat),
          i := 0, j := 0 } ∧
      InitFrame s t.mem ∧ t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = s.gpr .esi ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp := by
  unfold initValid
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok s (arg s 3) hp.scratchFit (hp.arg_in (i := 3) (by decide)) rfl hp.scratch)
    fun a ⟨ham, hak⟩ => ?_
  obtain haf : InitFrame s a.mem := by
    rw [ham]
    exact (savedMem_frame _ _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self
  obtain hasp : a.gpr .esp = s.gpr .esp := hak.gpr (by decide)
  obtain hb : WP isa (.block [.mov .edi (.mem (at_ .esp 12)), .mov .esi (imm 0)]) a fun b =>
      b.mem = a.mem ∧ b.rd = s.rd ∧ b.wr = s.wr ∧ b.gpr .edi = (arg s 2) ∧ b.gpr .esi = 0#32 ∧
        b.gpr .esp = s.gpr .esp := by
    obtain h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := hp.arg_in (i := 2) (by decide)
    obtain v12 : a.mem.readW (addr (s.gpr .esp) 12) 32 = (arg s 2) := hp.arg_eq haf (i := 2) (by decide)
    rrun [hasp, hak.2.1, hak.2.2, h12, v12]
  refine WP.mono hb fun b ⟨hbm, hbr, hbw, hbdi, hbsi, hbsp⟩ => ?_
  obtain hfit : (b.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [hbdi]; have := hp.ctxFit; omega_using [this]
  obtain hpb : InRegions b.wr ((b.gpr .edi).setWidth 64) 256 := by
    rw [hbw, hbdi]
    obtain h' := region_offset _ _ _ 0 256 (by decide) (by decide) hp.ctx
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h'
  obtain hib : IdentityInv b 0 b := ⟨by rw [identityMem_zero], rfl, rfl, rfl, rfl, hbsi⟩
  refine WP.seq (WP.mono (identity_loop b b (by decide) hfit hpb hib) fun c hc => ?_)
  obtain ⟨hcm, hcr, hcw, hcdi, hcsp, _⟩ := hc
  obtain hreset : WP isa (.block [.mov .esi (imm 0), .mov .ebx (imm 0), .mov .ebp (imm 0)]) c
      fun d => d.mem = c.mem ∧ d.rd = c.rd ∧ d.wr = c.wr ∧ d.gpr .edi = c.gpr .edi ∧
        d.gpr .esp = c.gpr .esp ∧ d.gpr .esi = 0#32 ∧ d.gpr .ebx = 0#32 ∧ d.gpr .ebp = 0#32 := by
    rrun
  refine WP.seq (WP.mono hreset fun d hd => ?_)
  obtain ⟨hdm, hdr, hdw, hddi, hdsp, hdsi, hdbx, hdbp⟩ := hd
  obtain hdf : InitFrame s d.mem := by
    rw [hdm, hcm, hbm, hbdi]
    exact haf.table (identityMem_frame _ _ _ (by decide))
  obtain hdC : d.gpr .edi = (arg s 2) := by rw [hddi, hcdi, hbdi]
  obtain hdS : d.gpr .esp = s.gpr .esp := by rw [hdsp, hcsp, hbsp]
  obtain hdrd : d.rd = s.rd := by rw [hdr, hcr, hbr]
  obtain hdwr : d.wr = s.wr := by rw [hdw, hcw, hbw]
  obtain hkey : keyOf d.mem (arg s 0) (arg s 1) = bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat := by
    unfold keyOf bytesAt
    apply List.map_congr_left
    intro k hk
    obtain hk' := List.mem_range.mp hk
    exact hdf _ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.keyCtx _ (Offset.contains_base _ (by omega_using [hk']) (by omega_using [hk']))
      · exact hp.keyScratch _ (Offset.contains_base _ (by omega_using [hk']) (by omega_using [hk']))
  obtain hpre : SchedulePre d (arg s 0) (arg s 1) := by
    refine ⟨hlen, by rw [hdC]; have := hp.ctxFit; omega_using [this], by rw [hdwr, hdC, ← hbdi, ← hbw]; exact hpb, ?_,
      hp.keyFit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdrd, hdwr]
      obtain ⟨r, hr, hc⟩ := hp.key
      exact ⟨r, List.mem_append_left _ hr, hc⟩
    · rw [hdC]
      exact fun x h₁ h₂ => hp.keyCtx x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega_using [h₂])
    · rw [hdrd, hdwr, hdS]; exact hp.arg_in (i := 0) (by decide)
    · rw [hdS]; exact hp.arg_eq hdf (i := 0) (by decide)
    · rw [hdrd, hdwr, hdS]; exact hp.arg_in (i := 1) (by decide)
    · rw [hdS]; exact hp.arg_eq hdf (i := 1) (by decide)
    · rw [hdS, hdC]; exact hp.arg_sep (i := 0) (by decide)
    · rw [hdS, hdC]; exact hp.arg_sep (i := 1) (by decide)
  obtain hid : ScheduleInv d (arg s 0) (arg s 1) 0 d := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · rw [hdm, hcm, hddi, hcdi, identityMem_table, schedule_zero]
    · rw [hdbp]; rfl
    · rw [hdsi]
    · rw [hdbx, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop d d _ _ (by decide) hpre hid) fun e he => ?_)
  obtain heC : e.gpr .edi = arg s 2 := by rw [he.p, hdC]
  obtain heS : e.gpr .esp = s.gpr .esp := by rw [he.sp, hdS]
  obtain herd : e.rd = s.rd := by rw [he.rd, hdrd]
  obtain hewr : e.wr = s.wr := by rw [he.wr, hdwr]
  rw [WP.block_append_iff]
  refine WP.mono (init_finish e (by rw [heC]; exact hp.ctxFit) (by rw [hewr, heC]; exact hp.ctx))
    fun f ⟨fax, fm, fk⟩ => ?_
  obtain hfS : f.gpr .esp = s.gpr .esp := (fk.gpr (by decide)).trans heS
  obtain hfrd : f.rd = s.rd := fk.2.1.trans herd
  obtain hfwr : f.wr = s.wr := fk.2.2.trans hewr
  obtain hctxf : Frame [⟨(arg s 2).setWidth 64, 258⟩] a.mem f.mem := by
    rw [fm, heC]
    refine frame_finish ?_ _ _
    obtain h1 := frame_of_table he.frame
    obtain h0 := frame_of_table (identityMem_frame a.mem ((arg s 2).setWidth 64) 256 (by decide))
    rw [hdm, hcm, hbm, hdC] at h1
    rw [hbdi] at h1
    exact h0.trans h1
  obtain hsaved : Saved f.mem (arg s 3) s := by
    obtain h0 := saved_savedMem s.mem (arg s 3) s
    rw [← ham] at h0
    refine h0.frame hctxf ?_
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact fun x h₁ h₂ => hp.ctxScratch x h₂ (by simp only [Region.Contains] at h₁ ⊢; omega_using [h₁])
  obtain hff : InitFrame s f.mem := by
    intro x hx
    rw [hctxf x (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hx _ List.mem_cons_self)]
    exact haf x hx
  refine WP.mono (restore_ok s f (arg s 3) hp.scratchFit
    (by rw [hfrd, hfwr, hfS]; exact hp.arg_in (i := 3) (by decide))
    (by rw [hfS]; exact hp.arg_eq hff (i := 3) (by decide))
    (by rw [hfrd, hfwr]; obtain ⟨r, hr, hc⟩ := hp.scratch; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    hsaved) fun g ⟨gbx, gsi, gdi, gbp, gm, gk⟩ => ?_
  refine ⟨(gk.gpr (by decide)).trans fax, ?_, by rw [gm]; exact hff, gbx, gsi, gdi, gbp⟩
  have ht := he.table
  rw [hdC] at ht
  rw [gm, fm, heC, context_finish, ht, ← keySchedule_eq, hkey]
  rfl

theorem valid_length32 (len : BitVec 32) :
    (len - 1#32).toNat < 256 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

theorem InitPre.transport {s t : State} (hp : InitPre s) (hm : t.mem = s.mem)
    (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : InitPre t := by
  obtain ha : ∀ i, arg t i = arg s i := fun i => by unfold arg argAddr; rw [hm, hsp]
  obtain hA : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [hsp]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrd, hA]; exact h1
  · simp only [hrd, ha]; exact h2
  · simp only [hwr, ha]; exact h3
  · simp only [hwr, ha]; exact h4
  · simp only [ha]; exact h5
  · simp only [ha]; exact h6
  · simp only [ha]; exact h7
  · rw [hsp]; exact h8
  · simp only [ha]; exact h9
  · simp only [ha]; exact h10
  · simp only [ha]; exact h11
  · simp only [ha, hA]; exact h12
  · simp only [ha, hA]; exact h13

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State) (hp : InitPre s) :
    WP isa VG.Impl.Rc4.X86.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) with
      | .ok ctx => t.gpr .eax = 0#32 ∧ contextAt t.mem ((arg s 2).setWidth 64) = ctx
      | .error .invalidKeyLength => t.gpr .eax = 1#32) ∧
      InitFrame s t.mem ∧ t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = s.gpr .esi ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp := by
  obtain h8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := hp.arg_in (i := 1) (by decide)
  obtain hcheck : WP isa (.block [.mov .eax (.mem (at_ .esp 8)), .alu .sub .eax (imm 1),
      .alu .cmp .eax (imm 256)]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Keep [.eax] s t ∧
      t.cf = some (decide ((arg s 1 - 1#32).toNat < 256)) := by
    refine WP.mono (WP.keep (Q := fun t => t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.cf = some (decide ((arg s 1 - 1#32).toNat < 256))) [.eax] ?_ (by decide +kernel))
      fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, hk, h.2.2.2⟩
    rrun [h8]
    exact rfl
  unfold VG.Impl.Rc4.X86.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, htk, htcf⟩ := ht
  obtain htp : InitPre t := hp.transport htm (htk.gpr (by decide)) htr htw
  obtain ha : ∀ i, arg t i = arg s i := fun i => by
    unfold arg argAddr; rw [htm, htk.gpr (r := .esp) (by decide)]
  let good := 1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256
  obtain hcond : isa.eval .ae t = some (decide (¬ good)) := by
    simp only [eval, htcf, Option.map_some]
    congr 1
    by_cases hg : good
    · rw [decide_eq_true ((valid_length32 _).mpr hg), decide_eq_false (not_not_intro hg)]
      rfl
    · rw [decide_eq_false (fun h => hg ((valid_length32 _).mp h)), decide_eq_true hg]
      rfl
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    refine WP.mono (WP.keep (Q := fun u => u.gpr .eax = 1#32 ∧ u.mem = t.mem) [.eax]
      (by rrun) (by decide +kernel)) fun u ⟨⟨hu, hum⟩, huk⟩ => ?_
    refine ⟨hu, by rw [hum, htm]; exact Frame.refl _ _, ?_, ?_, ?_, ?_⟩ <;>
      exact (huk.gpr (by decide)).trans (htk.gpr (by decide))
  · have hg : good := Classical.not_not.mp (of_decide_eq_false hy)
    change 1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    refine WP.mono (init_valid t htp (by rw [ha]; exact hg))
      fun u ⟨hu0, huc, huf, hbx, hsi, hdi, hbp⟩ => ?_
    simp only [InitFrame, ha, htm] at huc huf
    refine ⟨⟨hu0, huc⟩, huf, ?_, ?_, ?_, ?_⟩
    · exact hbx.trans (htk.gpr (by decide))
    · exact hsi.trans (htk.gpr (by decide))
    · exact hdi.trans (htk.gpr (by decide))
    · exact hbp.trans (htk.gpr (by decide))

end VG.Proof.Rc4.X86

end

end


/-!
# RC4 on x86 (32-bit): `Verified`

`init` and `apply` meet `initC` and `applyC`, with their arguments only
read; the shared contracts let the code write them too (`wideInit`,
`wideApply`), which `Verified.narrowTo` allows.
-/

@[expose] public section

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The registers the code writes. -/
def written : List Reg := [.eax, .ecx, .edx, .ebx, .esi, .edi, .ebp]

theorem callee_saved {s t : State} (hsp : t.gpr .esp = s.gpr .esp)
    (hbx : t.gpr .ebx = s.gpr .ebx) (hsi : t.gpr .esi = s.gpr .esi)
    (hdi : t.gpr .edi = s.gpr .edi) (hbp : t.gpr .ebp = s.gpr .ebp) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [hbx, hsi, hdi, hbp, hsp]

theorem init_correct (s : State) (hs : initC.pre s) :
    WP isa init s fun s' => abiPreserved s s' ∧ initC.post s s' := by
  obtain ⟨hrd, hwr, kc, ks, cs, ac, as, rc, rs, kfit, cfit, sfit, spfit⟩ := hs
  obtain hp : InitPre s :=
    { args := ⟨_, by rw [hrd]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        Region.contains_self _ _⟩
      key := ⟨_, by rw [hrd]; exact List.mem_cons_self, Region.contains_self _ _⟩
      ctx := ⟨_, by rw [hwr]; exact List.mem_cons_self, Region.contains_self _ _⟩
      scratch := ⟨_, by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        Region.contains_self _ _⟩
      keyFit := kfit, ctxFit := cfit, scratchFit := sfit, spFit := spfit
      keyCtx := kc, keyScratch := ks, ctxScratch := cs, argsCtx := ac, argsScratch := as }
  refine WP.mono (WP.keep written (init_ok s hp) (by lit_decide))
    fun t ⟨⟨hpost, hf, hbx, hsi, hdi, hbp⟩, hk⟩ => ⟨⟨callee_saved (hk.gpr (by decide)) hbx hsi hdi hbp, ?_⟩, ?_⟩
  · refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [rc, rs]
  · unfold initC
    dsimp only
    revert hpost
    cases Spec.Rc4.init (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) with
    | ok c => intro hpost; exact ⟨by rw [ret_low, hpost.1]; rfl, hpost.2⟩
    | error e => cases e; intro hpost; rw [ret_low, hpost]; rfl

theorem apply_correct (s : State) (hs : applyC.pre s) :
    WP isa apply s fun s' => abiPreserved s s' ∧ applyC.post s s' := by
  obtain hp := applyPre_of hs
  obtain ⟨_, _, _, _, _, _, _, _, rc, rd, rs, _⟩ := hs
  refine WP.mono (WP.keep written (apply_ok s hp) (by lit_decide))
    fun t ⟨⟨hpost, hf, hbx, hsi, hdi, hbp⟩, hk⟩ => ⟨⟨callee_saved (hk.gpr (by decide)) hbx hsi hdi hbp, ?_⟩, hpost⟩
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [applyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [rc, rd, rs]

def initRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩, ⟨argAddr s 0, 16⟩]
def initWr (s : State) : List Region := [⟨(arg s 2).setWidth 64, 258⟩, ⟨(arg s 3).setWidth 64, 64⟩]

def applyRd (s : State) : List Region := [⟨argAddr s 0, 16⟩]
def applyWr (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 258⟩, ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩,
    ⟨(arg s 3).setWidth 64, 64⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [VG.Proof.Rc4.X86.initC, VG.Proof.Rc4.X86.wideInit,
                     VG.Proof.Rc4.X86.applyC, VG.Proof.Rc4.X86.wideApply,
                     VG.Proof.Rc4.X86.initRd, VG.Proof.Rc4.X86.initWr,
                     VG.Proof.Rc4.X86.applyRd, VG.Proof.Rc4.X86.applyWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wideInit_pre (s : State) (h : wideInit.pre s) :
    initC.pre (s.withRegions (initRd s) (initWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem wideApply_pre (s : State) (h : wideApply.pre s) :
    applyC.pre (s.withRegions (applyRd s) (applyWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem init_verified : Verified target init (initScratchContract abi) := by
  have hsat := init_implies.sat_left
  obtain narrowSat : ∃ s, initC.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideInit_pre s hs⟩
  apply Verified.of_implies _ init_implies
  refine Verified.narrowTo (Verified.of_correct init_correct init_ct (.refl narrowSat))
    initRd initWr wideInit_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initRd, initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [initWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem apply_verified : Verified target apply (applyScratchContract abi) := by
  have hsat := apply_implies.sat_left
  obtain narrowSat : ∃ s, applyC.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wideApply_pre s hs⟩
  apply Verified.of_implies _ apply_implies
  refine Verified.narrowTo (Verified.of_correct apply_correct apply_ct (.refl narrowSat))
    applyRd applyWr wideApply_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [applyRd, applyWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [applyWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

end VG.Proof.Rc4.X86

end

end


/-!
# RC4 on x86, with the working space on the stack

`vg_rc4_init` and `vg_rc4_apply` keep our caller's `ebx`, `esi`, `edi` and
`ebp`, and `vg_rc4_apply` the secret `j`, in their working space: they run
their code, proved with it as an argument (`Verified.lean`), in a frame that
allocates it and copies their three argument slots (`Verified.stackScratch`):
84 bytes, 64 of working space, which their registrations zero before
returning (`Proof/Rc4/X86/Scrub.lean`). The code
uses no other stack. The copies are read only where the postconditions and
`vg_rc4_apply`'s leak, the context's `i`, read the buffers
(`Proof/Rc4/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.Rc4.X86

open VG VG.X86

/-- A state satisfying `vg_rc4_init`'s precondition: a 1-byte key at
`0x1000` and the context at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def initFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 1 else if a = 0x800d then 0x20 else 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 258⟩, ⟨0x8004, 12⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Rc4.initContract X86.abi 84).pre s := by
  implies_sat [Spec.Rc4.initContract, Spec.Rc4.initSig, Spec.Rc4.initPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] [initFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using initFrameSat

/-- A state satisfying `vg_rc4_apply`'s precondition: the context at
`0x1000` and 1 byte of data at `0x2000`, as stack arguments at `0x8004`,
which are writable. -/
def applyFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800c then 1 else 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩, ⟨0x8004, 12⟩]

theorem applyFrameSat_pre : ∃ s, (Spec.Rc4.applyContract X86.abi 84).pre s := by
  implies_sat [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost, Spec.Rc4.applyLeak,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [applyFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using applyFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 84 3 Impl.Rc4.X86.init)
      (Spec.Rc4.initContract X86.abi 84) :=
  X86.Verified.stackScratch (sig := Spec.Rc4.initSig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.initPost X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 84)
    init_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.initPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Rc4.initPostOut_local _ vs m m₁ m₂ r hl hb h) initFrameSat_pre

theorem apply_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 84 3 Impl.Rc4.X86.apply)
      (Spec.Rc4.applyContract X86.abi 84) :=
  X86.Verified.stackScratch (sig := Spec.Rc4.applySig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.applyPost X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 84)
    (leak := some (Spec.Rc4.applyLeak X86.abi.ptrBits))
    apply_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.applyPost_local _)
    (fun vs m m₁ m₂ r hl _ hb h => Proof.Rc4.applyPostOut_local _ vs m m₁ m₂ r hl hb h) applyFrameSat_pre (hleak := Proof.Rc4.applyLeak_local _)

end VG.Proof.Rc4.X86
