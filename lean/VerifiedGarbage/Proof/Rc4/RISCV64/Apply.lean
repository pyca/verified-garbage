module

import VerifiedGarbage.Proof.Rc4.RISCV64.ApplyLoop
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Rc4.Stream
public import VerifiedGarbage.Proof.Rc4.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Spec.Rc4

/-! # RC4 on RISC-V: the stream function

`apply` copies the table into its frame, runs the stream loop there
(`apply_loop`), copies it back with the PRGA indices, and zeroes the frame. -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4 VG.Proof.Rc4.Scan64

theorem bytes_congr {m m' : Mem} {d : Addr} {n : Nat}
    (h : ∀ i < n, m' (d + BitVec.ofNat 64 i) = m (d + BitVec.ofNat 64 i)) :
    bytesAt m' d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- A byte outside the one region of a frame. -/
theorem frame_byte {R : Region} {m m' : Mem} (hf : Frame [R] m m') {x : Addr}
    (hx : ¬ (x - R.base).toNat < R.len) : m' x = m x :=
  hf x fun r hr hc => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hx (by simp only [Region.Contains] at hc; omega)

/-- Copying 256 bytes, from `src` to `dst`, separate. -/
theorem copy256_ok (s : State) {src dst : Reg} (hs : Reg.t0 ≠ src) (hd : Reg.t0 ≠ dst)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr src) 256) (hw : InRegions s.wr (s.gpr dst) 256)
    (hsep : Mem.Sep (s.gpr dst) 256 (s.gpr src) 256) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 src dst 0 0 256)) s fun t =>
      (∀ k < 256, t.mem (s.gpr dst + BitVec.ofNat 64 k) = s.mem (s.gpr src + BitVec.ofNat 64 k)) ∧
      Frame [⟨s.gpr dst, 256⟩] s.mem t.mem ∧ (∀ r, r ≠ .t0 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.mono (Bytes.copyBytes_ok hs hd (by decide) (by decide)
    (fun i hi => by rw [Nat.zero_add]; exact region_offset _ _ _ _ _ (by omega) (by omega) hr)
    (fun i hi => by rw [Nat.zero_add]; exact region_offset _ _ _ _ _ (by omega) (by omega) hw)
    (fun i hi hc => ?_)) fun t ht => ?_
  · simp only [Region.Contains, Nat.zero_add, BitVec.add_zero] at hc
    exact hsep (s.gpr src + BitVec.ofNat 64 i) (by omega) (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hi)
  · refine ⟨fun k hk => by simpa only [Nat.zero_add] using ht.copied k hk, ?_, ht.gpr, ht.rd,
      ht.wr, ht.sp⟩
    have hf := ht.frame
    simp only [BitVec.add_zero] at hf
    exact hf

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258) :
    WP isa (.block [.load .b .a3 .a0 256, .load .b .t4 .a0 257, .li .t6 0]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.gpr .a0 = s.gpr .a0 ∧ t.gpr .a1 = s.gpr .a1 ∧ t.gpr .a2 = s.gpr .a2 ∧
      t.gpr .a3 = (s.mem (s.gpr .a0 + 256#64)).setWidth 64 ∧
      t.gpr .t4 = (s.mem (s.gpr .a0 + 257#64)).setWidth 64 ∧ t.gpr .t6 = 0#64 := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [h256, h257]

/-- Copying the table back to the context with the PRGA indices, and zeroing
the frame. -/
theorem apply_end (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hF : InRegions s.wr (s.gpr .a7) 256) (hp : InRegions s.wr (s.gpr .a0) 258)
    (hFc : Mem.Sep (s.gpr .a7) 256 (s.gpr .a0) 258) :
    WP isa (.block (Impl.Words.RISCV64.copyBytes .t0 .a7 .a0 0 0 256 ++
      ([.store .b .a3 .a0 256, .store .b .t4 .a0 257] : List Instr) ++ wipe)) s fun t =>
      (∀ k < 256, t.mem (s.gpr .a0 + BitVec.ofNat 64 k) = s.mem (s.gpr .a7 + BitVec.ofNat 64 k)) ∧
      t.mem (s.gpr .a0 + 256#64) = (s.gpr .a3).setWidth 8 ∧
      t.mem (s.gpr .a0 + 257#64) = (s.gpr .t4).setWidth 8 ∧
      ∀ x, ¬ (x - s.gpr .a0).toNat < 258 → ¬ (x - s.gpr .a7).toNat < 256 → t.mem x = s.mem x := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .a7) 256 := by
    obtain ⟨region, h, hc⟩ := hF
    exact ⟨region, List.mem_append_right _ h, hc⟩
  have hw : InRegions s.wr (s.gpr .a0) 256 := by
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hp
  have hsep : Mem.Sep (s.gpr .a0) 256 (s.gpr .a7) 256 := fun x hx hy => hFc x hy (by omega)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy256_ok s (by decide) (by decide) hr hw hsep) fun u ⟨uc, uf, ug, urd, uwr, usp⟩ => ?_
  have u0 : u.gpr .a0 = s.gpr .a0 := ug _ (by decide)
  have u7 : u.gpr .a7 = s.gpr .a7 := ug _ (by decide)
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hb : WP isa (.block [.store .b .a3 .a0 256, .store .b .t4 .a0 257]) u fun v =>
      v.mem = (u.mem.write (s.gpr .a0 + 256#64) 1 ((s.gpr .a3).setWidth 8)).write
        (s.gpr .a0 + 257#64) 1 ((s.gpr .t4).setWidth 8) ∧ v.gpr = u.gpr ∧ v.rd = u.rd ∧
        v.wr = u.wr ∧ v.sp = u.sp := by
    have h256' : InRegions u.wr (s.gpr .a0 + BitVec.ofNat 64 256) 1 := by rw [uwr]; exact h256
    have h257' : InRegions u.wr (s.gpr .a0 + BitVec.ofNat 64 257) 1 := by rw [uwr]; exact h257
    rrun [h256', h257', u0, ug _ (show Reg.a3 ≠ .t0 by decide), ug _ (show Reg.t4 ≠ .t0 by decide)]
  refine WP.mono hb fun v ⟨vm, vg, vrd, vwr, vsp⟩ => ?_
  have v7 : v.gpr .a7 = s.gpr .a7 := by rw [vg, u7]
  refine WP.mono (wipe_ok v (by rw [v7]; exact hal) (by rw [vwr, uwr, v7]; exact hF))
    fun t ⟨tf, _, _, _, _⟩ => ?_
  rw [v7] at tf
  have hne (k : Nat) (hk : k < 256) (e : Nat) (he : 256 ≤ e) (he' : e < 258) :
      s.gpr .a0 + BitVec.ofNat 64 k ≠ s.gpr .a0 + BitVec.ofNat 64 e :=
    Offset.add_ofNat_ne _ (by omega) (by omega) (by omega)
  have hout (k : Nat) (hk : k < 258) : ¬ (s.gpr .a0 + BitVec.ofNat 64 k - s.gpr .a7).toNat < 256 :=
    fun h => hFc _ h (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hk)
  refine ⟨fun k hk => ?_, ?_, ?_, fun x hx hx' => ?_⟩
  · rw [frame_byte tf (hout k (by omega)), vm, write_byte, ite_eq_right (hne k hk 257 (by decide) (by decide)),
      write_byte, ite_eq_right (hne k hk 256 (by decide) (by decide)), uc k hk]
  · rw [frame_byte tf (hout 256 (by decide)), vm, write_byte,
      ite_eq_right (Offset.add_ofNat_ne _ (by decide) (by decide) (by decide)), write_byte, ite_eq_left rfl]
  · rw [frame_byte tf (hout 257 (by decide)), vm, write_byte, ite_eq_left rfl]
  · have h1 : x ≠ s.gpr .a0 + 256#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    have h2 : x ≠ s.gpr .a0 + 257#64 := by
      intro he; apply hx; rw [he, Mem.sub_ofNat_toNat _ (by decide)]; decide
    rw [frame_byte tf hx', vm, write_byte, ite_eq_right h2, write_byte, ite_eq_right h1,
      frame_byte uf (by simp only; omega)]

/-- `applyMain`, with its frame at the stack pointer, from the PRGA indices
loaded. -/
theorem apply_main (s : State) (n : Nat) (hbound : n + 1 < 2 ^ 64)
    (hlen : s.gpr .a2 = BitVec.ofNat 64 (n + 1))
    (h3 : s.gpr .a3 = (s.mem (s.gpr .a0 + 256#64)).setWidth 64)
    (h4 : s.gpr .t4 = (s.mem (s.gpr .a0 + 257#64)).setWidth 64) (h6 : s.gpr .t6 = 0#64)
    (hal : s.sp.toNat % 8 = 0) (hF : InRegions s.wr s.sp 256)
    (hp : InRegions s.wr (s.gpr .a0) 258)
    (hd : InRegions s.wr (s.gpr .a1) (n + 1))
    (hs : Mem.Sep (s.gpr .a0) 258 (s.gpr .a1) (n + 1))
    (hFc : Mem.Sep s.sp 256 (s.gpr .a0) 258)
    (hFd : Mem.Sep s.sp 256 (s.gpr .a1) (n + 1)) :
    WP isa applyMain s fun t =>
      let result := update (contextAt s.mem (s.gpr .a0)) (bytesAt s.mem (s.gpr .a1) (n + 1))
      contextAt t.mem (s.gpr .a0) = result.1 ∧ bytesAt t.mem (s.gpr .a1) (n + 1) = result.2 := by
  have hpRead : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold applyMain
  refine WP.seq (Wp.wp_addSp (by decide) fun b hb => ?_)
  have b7 : b.gpr .a7 = s.sp := by rw [hb.gpr, BitVec.add_zero]
  have b0 : b.gpr .a0 = s.gpr .a0 := hb.other _ (by decide)
  have hbr : InRegions (b.rd ++ b.wr) (b.gpr .a0) 256 := by
    rw [hb.rd, hb.wr, b0]
    simpa only [BitVec.add_zero] using region_offset _ _ _ 0 256 (by decide) (by decide) hpRead
  refine WP.mono (copy256_ok b (src := .a0) (dst := .a7) (by decide) (by decide) hbr
    (by rw [hb.wr, b7]; exact hF)
    (by rw [b7, b0]; exact fun x hx hy => hFc x hx (by omega)))
    fun c ⟨cc, cf, cg, crd, cwr, csp⟩ => ?_
  rw [b7, b0, hb.mem] at cc
  rw [b7, hb.mem] at cf
  have c7 : c.gpr .a7 = s.sp := (cg _ (by decide)).trans b7
  have c0 : c.gpr .a0 = s.gpr .a0 := (cg _ (by decide)).trans b0
  have c1 : c.gpr .a1 = s.gpr .a1 := (cg _ (by decide)).trans (hb.other _ (by decide))
  have c2 : c.gpr .a2 = s.gpr .a2 := (cg _ (by decide)).trans (hb.other _ (by decide))
  have c3 : c.gpr .a3 = s.gpr .a3 := (cg _ (by decide)).trans (hb.other _ (by decide))
  have c4 : c.gpr .t4 = s.gpr .t4 := (cg _ (by decide)).trans (hb.other _ (by decide))
  have c6 : c.gpr .t6 = s.gpr .t6 := (cg _ (by decide)).trans (hb.other _ (by decide))
  have cw : c.wr = s.wr := by rw [cwr, hb.wr]
  have hdata : bytesAt c.mem (s.gpr .a1) (n + 1) = bytesAt s.mem (s.gpr .a1) (n + 1) :=
    bytes_congr fun i hi => frame_byte cf fun h =>
      hFd _ h (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hi)
  let ctx := contextAt s.mem (s.gpr .a0)
  refine WP.seq (WP.mono (apply_loop n c ctx hbound
    (by rw [c7]; exact table_copy cc) (c3.trans h3) (c4.trans h4) (c6.trans h6)
    (by rw [c7]; exact hal) (c2.trans hlen)
    (by rw [cw, c7]; exact hF) (by rw [cw, c1]; exact hd) (by rw [c7, c1]; exact hFd))
    fun e he => ?_)
  have e7 : e.gpr .a7 = s.sp := he.p.trans c7
  have e0 : e.gpr .a0 = s.gpr .a0 := he.ctx.trans c0
  have ew : e.wr = s.wr := he.wr.trans cw
  refine WP.mono (apply_end e (by rw [e7]; exact hal) (by rw [ew, e7]; exact hF)
    (by rw [ew, e0]; exact hp) (by rw [e7, e0]; exact hFc)) fun t ⟨ttab, ti, tj, tout⟩ => ?_
  rw [e0, e7] at ttab
  rw [e0] at ti tj tout
  rw [e7] at tout
  have htab := he.table
  have hi := he.i
  have hj := he.j
  have hdat := he.data
  rw [c7] at htab
  rw [c1, hdata] at htab hi hj hdat
  refine ⟨context_of (by rw [table_copy ttab, htab]) (by rw [ti, hi, low_byte])
    (by rw [tj, hj, low_byte]), ?_⟩
  rw [← hdat]
  exact bytes_congr fun i hi => tout _
    (fun h => hs _ h (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hi))
    (fun h => hFd _ h (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hi))

/-- The stream function, in its frame of 256 bytes below the stack pointer. -/
theorem apply_ok (s : State) (hal : s.sp.toNat % 16 = 0) (hsp : 256 ≤ s.sp.toNat)
    (hp : InRegions s.wr (s.gpr .a0) 258)
    (hd : InRegions s.wr (s.gpr .a1) (s.gpr .a2).toNat)
    (hs : Mem.Sep (s.gpr .a0) 258 (s.gpr .a1) (s.gpr .a2).toNat)
    (hFc : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a0) 258)
    (hFd : Mem.Sep (s.sp - 256#64) 256 (s.gpr .a1) (s.gpr .a2).toNat) :
    WP isa VG.Impl.Rc4.RISCV64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .a0))
        (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
      contextAt t.mem (s.gpr .a0) = result.1 ∧
        bytesAt t.mem (s.gpr .a1) (s.gpr .a2).toNat = result.2 := by
  have hpRead : InRegions (s.rd ++ s.wr) (s.gpr .a0) 258 := by
    obtain ⟨region, hr, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hr, hc⟩
  unfold VG.Impl.Rc4.RISCV64.apply
  refine WP.seq (WP.mono (apply_start s hpRead) fun a ha => ?_)
  obtain ⟨ham, har, haw, hasp, ha0, ha1, ha2, ha3, ha4, ha6⟩ := ha
  refine WP.ite (s.gpr .a2 == 0) (by rw [Steps.eval_zero, ha2]) (fun hz => ?_) (fun hnz => ?_)
  · have hz' : s.gpr .a2 = 0 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz', ham]
    exact ⟨context_ext rfl rfl rfl, rfl⟩
  · have hnz' : s.gpr .a2 ≠ 0 := beq_eq_false_iff_ne.mp hnz
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (show (s.gpr .a2).toNat ≠ 0 by
      intro h; exact hnz' (BitVec.eq_of_toNat_eq h))
    change (s.gpr .a2).toNat = n + 1 at hnEq
    have hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .a2).isLt
    rw [hnEq]
    rw [hnEq] at hd hs hFd
    have hF : (s.sp - 256#64).toNat = s.sp.toNat - 256 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega)]; rfl
    refine WP.alloc (n := frameBytes) (by decide) (by rw [hasp]; exact hsp) ?_
    have hsp' : (allocd frameBytes a).sp = s.sp - 256#64 := by
      show a.sp - BitVec.ofNat 64 256 = _
      rw [hasp]
    have hg : (allocd frameBytes a).gpr = a.gpr := rfl
    have hm : (allocd frameBytes a).mem = a.mem := rfl
    have hw : (allocd frameBytes a).wr = ⟨s.sp - 256#64, 256⟩ :: s.wr := by
      show (⟨a.sp - BitVec.ofNat 64 256, 256⟩ :: a.wr : List Region) = _
      rw [hasp, haw]
    have hwr (r : Region) (h : r ∈ s.wr) : r ∈ (allocd frameBytes a).wr := by
      rw [hw]; exact List.mem_cons_of_mem _ h
    refine WP.mono (apply_main (allocd frameBytes a) n hbound
      (by rw [hg, ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [hg, hm, ha3, ha0, ham]) (by rw [hg, hm, ha4, ha0, ham]) (by rw [hg, ha6])
      (by rw [hsp', hF]; omega)
      ⟨⟨s.sp - 256#64, 256⟩, by rw [hw]; exact List.mem_cons_self,
        by rw [hsp']; exact Region.contains_self _ _⟩
      (by obtain ⟨r, hr, hc⟩ := hp; exact ⟨r, hwr r hr, by rw [hg, ha0]; exact hc⟩)
      (by obtain ⟨r, hr, hc⟩ := hd; exact ⟨r, hwr r hr, by rw [hg, ha1]; exact hc⟩)
      (by rw [hg, ha0, ha1]; exact hs) (by rw [hsp', hg, ha0]; exact hFc)
      (by rw [hsp', hg, ha1]; exact hFd)) fun u hu => ?_
    rw [hg, hm, ha0, ha1, ham] at hu
    exact hu

end VG.Proof.Rc4.RISCV64
