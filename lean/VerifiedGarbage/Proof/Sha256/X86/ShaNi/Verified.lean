module

public import VerifiedGarbage.Proof.Sha256.X86.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
public import VerifiedGarbage.Impl.Sha256.X86.ShaNi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.X86.Contract
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Lit
meta import VerifiedGarbage.Impl.Sha256.X86.ShaNi
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Compress
public import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Memory
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Sha256.X86.Compress
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Compress
meta import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Memory
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! ### `Sha256.X86.ShaNi.Whole`, which this module and modules that import it used -/

section

/-! ### `Sha256.X86.ShaNi.Load`, which this module and modules that import it used -/

section

/-! ### `Sha256.X86.ShaNi.Block`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (workRegion)
open VG.Proof.Sha256.X86 (Pre st bp nb scr esp₀ stR blR scrR H₀ blkAddr blk Saved
  contains_sub work_sub saved_frame blk_word compressBlocks_succ)
open VG.Spec.Sha256 (HashValue Block stateAt compressBlocks)

theorem Pre.scr_vec {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d + 16 ≤ 112) :
    InRegions s₀.wr (addr (scr s₀) d) 16 :=
  ⟨scrR s₀, by simp [hp.wr],
    contains_sub hd (by omega_using [hd]) (hp.scr_eq (by omega_using [hd]))⟩

theorem Pre.blk_fit {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).toNat + 64 ≤ 2 ^ 32 := by
  have hb := hp.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 64 * i < 2 ^ 32 by omega_using [hi, hb]),
    Nat.mod_eq_of_lt (show (bp s₀).toNat + 64 * i < 2 ^ 32 by omega_using [hi, hb])]
  omega_using [hi, hb]

theorem Pre.blk_vec {s₀ : State} (hp : Pre s₀) {i n : Nat}
    (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) ((blkAddr s₀ i).setWidth 64 + BitVec.ofNat 64 (16 * n)) 16 := by
  have he : (blkAddr s₀ i).setWidth 64 =
      (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i) := by
    simpa only [blkAddr, addr] using addr_eq (x := bp s₀) (k := 64 * i)
      (by have := hp.blk_fits; omega_using [hi, this])
  refine ⟨blR s₀, by simp only [hp.rd, List.mem_append, List.mem_cons, true_or], ?_⟩
  rw [he, Offset.add_add]
  exact Offset.contains_base _ (by omega_using [hi, hn]) (by have := hp.blk_fits; omega_using [hi, hn, this])

theorem work_write128 (p : BitVec 32) (hfit : p.toNat + 112 ≤ 2 ^ 32)
    (m : Mem) (v : BitVec 128) {d : Nat} (hd : d + 16 ≤ 96) :
    Frame [workRegion p] m (m.writeW (addr p d) v) := by
  refine (Frame.refl _ _).writeW (List.mem_singleton_self _) v ?_
  rw [addr_eq (by omega_using [hfit, hd])]
  exact Offset.contains_base _ hd (by omega_using [hd])

theorem saveHash_frame (s : State) (hfit : (s.gpr .esi).toNat + 112 ≤ 2 ^ 32) :
    Frame [workRegion (s.gpr .esi)] s.mem
      ((s.mem.writeW (addr (s.gpr .esi) 32) (s.xmm .xmm1)).writeW
        (addr (s.gpr .esi) 48) (s.xmm .xmm2)) :=
  (work_write128 _ hfit _ _ (d := 32) (by decide)).trans
    (work_write128 _ hfit _ _ (d := 48) (by decide))

structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = abef (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  x2 : s.xmm .xmm2 = cdgh (compressBlocks (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i)
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  ebx : s.gpr .ebx = st s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  mask : s.mem.readW (addr (scr s₀) 16) 128 = bswapMask

structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  ebp : s.gpr .ebp = BitVec.ofNat 32 (nb s₀ - i)

theorem saveHash_reads (p : BitVec 32) (hfit : p.toNat + 112 ≤ 2 ^ 32)
    (m : Mem) (x y : BitVec 128) :
    let m' := (m.writeW (addr p 32) x).writeW (addr p 48) y
    m'.readW (addr p 32) 128 = x ∧ m'.readW (addr p 48) 128 = y ∧
      m'.readW (addr p 16) 128 = m.readW (addr p 16) 128 := by
  have sep : ∀ d e : Nat, d + 16 ≤ 112 → e + 16 ≤ 112 →
      d + 16 ≤ e ∨ e + 16 ≤ d → Mem.Sep (addr p d) 16 (addr p e) 16 := by
    intro d e hd he hde
    rw [addr_eq (by omega_using [hfit, hd]), addr_eq (by omega_using [hfit, he])]
    exact Offset.sep _ hde (by omega_using [hd]) (by omega_using [he])
  dsimp only
  rw [Mem.readW_writeW_sep (sep 32 48 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self m _ 16 x (by decide), Mem.readW_writeW_self _ _ 16 y (by decide),
    Mem.readW_writeW_sep (sep 16 48 (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep 16 32 (by decide) (by decide) (by decide)) (by decide)]
  exact ⟨rfl, rfl, rfl⟩

theorem in_read_of_write {rd wr : List Region} {p : Addr} {n : Nat}
    (h : InRegions wr p n) : InRegions (rd ++ wr) p n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append.mpr (.inr hr), hc⟩

theorem body_step {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      Common s₀ (i + 1) s' ∧ s'.gpr .edi = blkAddr s₀ (i + 1) ∧
      s'.gpr .ebp = BitVec.ofNat 32 (nb s₀ - (i + 1)) ∧
      s'.zf = some (BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0) := by
  have vecwr : ∀ d : Nat, d + 16 ≤ 112 → InRegions s.wr (addr (s.gpr .esi) d) 16 := by
    intro d hd; rw [hL.wr, hL.esi]; exact Pre.scr_vec hp hd
  refine WP.seq (WP.mono (saveHash_ok s (vecwr 32 (by decide)) (vecwr 48 (by decide)))
    fun s₁ ⟨hm₁, hx₁, hg₁, hrd₁, hwr₁⟩ => ?_)
  have hf₁ : Frame [workRegion (scr s₀)] s.mem s₁.mem := by
    rw [hm₁]
    have hf := saveHash_frame s (by rw [hL.esi]; exact hp.scr_fits)
    simpa only [hL.esi] using hf
  have hf₁full : Frame [stR s₀, scrR s₀] s.mem s₁.mem := hf₁.sub
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨scrR s₀, by simp, work_sub _⟩)
  have hf : Frame [stR s₀, scrR s₀] s₀.mem s₁.mem := hL.frame.trans hf₁full
  have hdi₁ : s₁.gpr .edi = blkAddr s₀ i := (congrFun hg₁ _).trans hL.edi
  have hsi₁ : s₁.gpr .esi = scr s₀ := (congrFun hg₁ _).trans hL.esi
  have savedValues := saveHash_reads (scr s₀) hp.scr_fits s.mem (s.xmm .xmm1) (s.xmm .xmm2)
  have vals : s₁.mem.readW (addr (scr s₀) 32) 128 = s.xmm .xmm1 ∧
      s₁.mem.readW (addr (scr s₀) 48) 128 = s.xmm .xmm2 ∧
      s₁.mem.readW (addr (scr s₀) 16) 128 = bswapMask := by
    rw [hm₁, hL.esi]
    exact ⟨savedValues.1, savedValues.2.1, savedValues.2.2.trans hL.mask⟩
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) (scr s₀) s₁ hdi₁ hsi₁
    (Pre.blk_fit hp hi) (by have := hp.scr_fits; omega_using [this])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.blk_vec hp hi hn)
    (by rw [hrd₁, hwr₁, hL.rd, hL.wr, ← hp.scr_eq (by decide)];
        exact in_read_of_write (Pre.scr_vec hp (d := 16) (by decide)))
    (by rw [← hp.scr_eq (by decide)]; exact vals.2.2)
    (fun t ht => by
      have ea : addr (blkAddr s₀ i) (4 * t) =
          (blkAddr s₀ i).setWidth 64 + BitVec.ofNat 64 (4 * t) :=
        addr_eq (by have := Pre.blk_fit hp hi; omega_using [ht, this])
      rw [← ea, hf.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
      exact blk_word hp hi ht)
    (by rw [hx₁]; exact hL.x1) (by rw [hx₁]; exact hL.x2) 16 (Nat.le_refl _))
    fun s₂ hR => ?_)
  have hsi₂ : s₂.gpr .esi = scr s₀ := (hR.gpr _ (by decide)).trans hsi₁
  have hg₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr =>
    (hR.gpr r hr).trans (congrFun hg₁ r)
  refine WP.mono (finishBlock_ok s₂ _ _ hR.x1 hR.x2
    (by rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hsi₂];
        exact in_read_of_write (Pre.scr_vec hp (d := 32) (by decide)))
    (by rw [hR.rd, hR.wr, hrd₁, hwr₁, hL.rd, hL.wr, hsi₂];
        exact in_read_of_write (Pre.scr_vec hp (d := 48) (by decide)))
    (by rw [hsi₂, hR.mem, vals.1]; exact hL.x1)
    (by rw [hsi₂, hR.mem, vals.2.1]; exact hL.x2))
    fun s₃ ⟨f1, f2, fdi, fbp, fg, fzf, fm, frd, fwr⟩ => ?_
  have mem : s₃.mem = s₁.mem := fm.trans hR.mem
  have ebp : s₂.gpr .ebp - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [hg₂ _ (by decide), hL.ebp,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega_using [hi]), Nat.sub_sub]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fbp.trans ebp, ?_⟩
  · rw [f1, compressBlocks_succ]
  · rw [f2, compressBlocks_succ]
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.esi
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.esp
  · rw [fg _ (by decide) (by decide), hg₂ _ (by decide)]; exact hL.ebx
  · exact frd.trans (hR.rd.trans (hrd₁.trans hL.rd))
  · exact fwr.trans (hR.wr.trans (hwr₁.trans hL.wr))
  · rw [mem]; exact hf
  · rw [mem]; exact saved_frame hp hL.saved (.inl hf₁)
  · rw [mem]; exact vals.2.2
  · rw [fdi, hg₂ _ (by decide), hL.edi, blkAddr, blkAddr, BitVec.add_assoc]
    rw [show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
    exact congrArg (fun n => bp s₀ + BitVec.ofNat 32 n) (by omega_using [])
  · rw [fzf, ebp]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.mono (body_step hp hi hL) fun s' ⟨hc, hdi, hbp, hz⟩ => ?_
  have hev : eval .ne s' = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    simp only [eval, hz, Option.map_some]
  by_cases hlast : i + 1 = nb s₀
  · exact .inl ⟨by rw [hev, hlast]; simp, hlast ▸ hc⟩
  · have hne : nb s₀ - (i + 1) ≠ 0 := by omega_using [hi, hlast]
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      have hn : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hn)] at h'
      exact hne h'
    exact .inr ⟨by rw [hev]; simpa using h0, by omega_using [hi, hlast], { hc with edi := hdi, ebp := hbp }⟩

theorem loop_ok {s₀ : State} (hp : Pre s₀) (hpos : 0 < nb s₀) {s : State}
    (hL : LInv s₀ 0 s) :
    WP isa (.loop body .ne) s (Common s₀ (nb s₀)) := by
  let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
  have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
    rintro m s ⟨i, rfl, hi, hL⟩
    refine WP.mono (body_ok hp hi hL) fun s' h => ?_
    rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
    · exact .inl ⟨he, hc⟩
    · exact .inr ⟨he, nb s₀ - (i + 1), by omega_using [hi], i + 1, rfl, hi', hL'⟩
  exact WP.loop (M := isa) Inv hstep (nb s₀) s ⟨0, rfl, hpos, hL⟩

end VG.Proof.Sha256.X86.ShaNi

end

end


@[expose] public section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (Pre st scr esp₀ stR scrR H₀ stAddr workRegion work_sub saved_frame
  contains_sub stateAt_eq stateAt_get)
open VG.Spec.Sha256 (stateAt compressBlocks)

theorem loadPointer_ok (s : State) (p : BitVec 32)
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 4) 32 = p) :
    WP isa (.block [.mov .ebx (.mem (at_ .esp 4))]) s fun s' =>
      s'.gpr .ebx = p ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, isa, State.load32,
    ea_at, hin, ite_true, hv, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg]
  exact ⟨trivial, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, trivial, trivial, trivial, trivial⟩

theorem storeMask_ok (s : State)
    (hout : InRegions s.wr (addr (s.gpr .esi) 16) 16) :
    WP isa (.block [.movdquStore (at_ .esi 16) .xmm0]) s fun s' =>
      s'.mem = s.mem.writeW (addr (s.gpr .esi) 16) (s.xmm .xmm0) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128, ea_at,
    hout, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem load_ok {s₀ : State} (hp : Pre s₀) {s : State}
    (hc : VG.Proof.Sha256.X86.Common s₀ 0 s) :
    WP isa (.block load) s fun s' =>
      Common s₀ 0 s' ∧ (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.zf = s.zf := by
  have shape : load = [.mov .ebx (.mem (at_ .esp 4))] ++
      (const bswapMask ++ (([.movdquStore (at_ .esi 16) .xmm0] : List Instr) ++ loadState)) := by
    simp only [load, List.append_assoc]
  rw [shape, WP.block_append_iff]
  refine WP.mono (loadPointer_ok s (st s₀)
    (by rw [hc.esp, hc.rd, hc.wr]; exact hp.in_arg (by decide) (by decide))
    (by rw [hc.esp]; exact hp.arg_frame hc.frame (i := 0) (by decide)))
    fun s₁ ⟨hb₁, hg₁, hm₁, hrd₁, hwr₁, hz₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok bswapMask s₁)
    fun s₂ ⟨h0, hx₂, hg₂, hm₂, hrd₂, hwr₂, hz₂⟩ => ?_
  have hsi₂ : s₂.gpr .esi = scr s₀ := (hg₂ _ (by decide)).trans ((hg₁ _ (by decide)).trans hc.esi)
  rw [WP.block_append_iff]
  refine WP.mono (storeMask_ok s₂
    (by rw [hsi₂, hwr₂, hwr₁, hc.wr]; exact Pre.scr_vec hp (by decide)))
    fun s₃ ⟨hm₃, hg₃, hrd₃, hwr₃, hz₃⟩ => ?_
  have hmem : s₃.mem = s.mem.writeW (addr (scr s₀) 16) bswapMask := by
    rw [hm₃, hm₂, hm₁, hsi₂, h0]
  have hframe : Frame [workRegion (scr s₀)] s.mem s₃.mem := by
    rw [hmem]; exact work_write128 _ hp.scr_fits _ _ (by decide)
  have hframeFull : Frame [stR s₀, scrR s₀] s.mem s₃.mem := hframe.sub
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨scrR s₀, by simp, work_sub _⟩)
  have state : stateAt s₃.mem ((st s₀).setWidth 64) =
      compressBlocks (H₀ s₀) s₀.mem ((VG.Proof.Sha256.X86.bp s₀).setWidth 64) 0 := by
    apply stateAt_eq hp
    intro k hk
    rw [hframe.readW (contains_sub (len := 32) (off := 4 * k) (by omega_using [hk]) (by omega_using [hk])
      (hp.stAddr_eq hk)) (by simpa using hp.st_scr.sub_right (work_sub _)) (by decide),
      ← stateAt_get hp s.mem hk, hc.state]
  have hb₃ : s₃.gpr .ebx = st s₀ := by rw [hg₃, hg₂ _ (by decide), hb₁]
  have rd₃ : s₃.rd = s₀.rd := hrd₃.trans (hrd₂.trans (hrd₁.trans hc.rd))
  have wr₃ : s₃.wr = s₀.wr := hwr₃.trans (hwr₂.trans (hwr₁.trans hc.wr))
  have out0 : InRegions s₀.wr ((st s₀).setWidth 64) 16 :=
    ⟨stR s₀, by simp [hp.wr], by simpa only [BitVec.add_zero] using
      (Offset.contains_base ((st s₀).setWidth 64) (d := 0) (n := 16) (k := 32) (by decide) (by decide))⟩
  have out16 : InRegions s₀.wr ((st s₀).setWidth 64 + BitVec.ofNat 64 16) 16 :=
    ⟨stR s₀, by simp [hp.wr], Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.mono (loadState_ok s₃ (by rw [hb₃]; exact hp.st_fits)
    (by rw [hb₃, rd₃, wr₃]; exact in_read_of_write out0)
    (by rw [hb₃, rd₃, wr₃]; exact in_read_of_write out16))
    fun s₄ ⟨x1, x2, hz₄, hg₄, hm₄, hrd₄, hwr₄⟩ => ?_
  have regs : ∀ r, r ≠ .eax → r ≠ .ebx → s₄.gpr r = s.gpr r :=
    fun r ha hb => (congrFun hg₄ r).trans ((congrFun hg₃ r).trans ((hg₂ r ha).trans (hg₁ r hb)))
  refine ⟨⟨?_, ?_, (regs _ (by decide) (by decide)).trans hc.esi,
    (regs _ (by decide) (by decide)).trans hc.esp, ?_, hrd₄.trans rd₃, hwr₄.trans wr₃,
    ?_, ?_, ?_⟩, regs, hz₄.trans (hz₃.trans (hz₂.trans hz₁))⟩
  · rw [x1, hb₃, state]
  · rw [x2, hb₃, state]
  · rw [hg₄]; exact hb₃
  · rw [hm₄]; exact hc.frame.trans hframeFull
  · rw [hm₄]; exact saved_frame hp hc.saved (.inl hframe)
  · rw [hm₄, hmem]; exact Mem.readW_writeW_self _ _ 16 _ (by decide)

end VG.Proof.Sha256.X86.ShaNi

end

end

@[expose] public section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Proof.Sha256.X86 (Pre pre_of st scr bp nb esp₀ stR scrR retR H₀
  save_ok common_zero restore_ok saved_frame)
open VG.Spec.Sha256 (stateAt compressBlocks)

theorem state_write_frame (p : Addr) (m : Mem) (x y : BitVec 128) :
    Frame [⟨p, 32⟩] m ((m.writeW p x).writeW (p + BitVec.ofNat 64 16) y) := by
  have c0 : (⟨p, 32⟩ : Region).Contains p 16 := by
    simpa only [BitVec.add_zero] using
      (Offset.contains_base p (d := 0) (n := 16) (k := 32) (by decide) (by decide))
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) x c0).writeW
    (List.mem_singleton_self _) y (Offset.contains_base _ (by decide) (by decide))

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.Sha256.X86.ShaNi.compress s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Sha256.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (save_ok hp)
    fun s₁ ⟨hesi, hedi, hebp, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (load_ok hp (common_zero hp hesi hesp hrd hwr hm))
    fun s₂ ⟨hc₀, hg, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₃ hc => ?_)
  · refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0)
      (by simp only [eval, hzf, hz]) (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by
        simp only [BitVec.and_self, beq_iff_eq] at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      refine loop_ok hp hpos { hc₀ with edi := ?_, ebp := ?_ }
      · rw [hg _ (by decide) (by decide), hedi]; simp [VG.Proof.Sha256.X86.blkAddr]
      · rw [hg _ (by decide) (by decide), hebp]; simp [nb]
  · rw [WP.block_append_iff]
    have out0 : InRegions s₃.wr ((st s₀).setWidth 64) 16 :=
      ⟨stR s₀, by simp [hc.wr, hp.wr], by simpa only [BitVec.add_zero] using
        (Offset.contains_base ((st s₀).setWidth 64) (d := 0) (n := 16) (k := 32) (by decide) (by decide))⟩
    have out16 : InRegions s₃.wr ((st s₀).setWidth 64 + BitVec.ofNat 64 16) 16 :=
      ⟨stR s₀, by simp [hc.wr, hp.wr], Offset.contains_base _ (by decide) (by decide)⟩
    refine WP.mono (store_ok s₃ _ hc.x1 hc.x2 (by rw [hc.ebx]; exact hp.st_fits)
      (by rw [hc.ebx]; exact out0) (by rw [hc.ebx]; exact out16))
      fun s₄ ⟨⟨x, y, hm₄⟩, hstate, hg₄, hrd₄, hwr₄⟩ => ?_
    have hf : Frame [stR s₀] s₃.mem s₄.mem := by
      rw [hm₄, hc.ebx]; exact state_write_frame _ _ _ _
    have hfFull : Frame [stR s₀, scrR s₀] s₃.mem s₄.mem := hf.sub
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        exact ⟨stR s₀, by simp, fun _ h => h⟩)
    have hs : VG.Proof.Sha256.X86.Common s₀ (nb s₀) s₄ :=
      ⟨(congrFun hg₄ _).trans hc.esi, (congrFun hg₄ _).trans hc.esp,
        hrd₄.trans hc.rd, hwr₄.trans hc.wr, hc.frame.trans hfFull,
        by rw [hc.ebx] at hstate; exact hstate,
        saved_frame hp hc.saved (.inr hf)⟩
    refine WP.mono (restore_ok hp hs) fun s₅ ⟨hr, hm₅⟩ => ⟨⟨hr, ?_⟩, ?_⟩
    · rw [hm₅]
      exact hs.frame.readW (Region.contains_self _ _)
        (by simpa using ⟨hp.ret_st, hp.ret_scr⟩) (by decide)
    · show stateAt s₅.mem _ = _
      rw [hm₅]; exact hs.state

end VG.Proof.Sha256.X86.ShaNi

end

end

@[expose] public section

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86

theorem compress_verified :
    Verified X86.target Impl.Sha256.X86.ShaNi.compress Proof.Sha256.compressX86 :=
  ⟨fun s hs => correct (VG.Proof.Sha256.X86.pre_of s hs),
    VG.Taint.constantTime (A := sseTaint) VG.Proof.Sha256.X86.τ₀
      (fun _ _ h₁ h₂ hpub => VG.Proof.Sha256.X86.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨VG.Proof.Sha256.X86.satState, VG.Proof.Sha256.X86.sat_pre⟩⟩

theorem compress_nosp : NoSp Impl.Sha256.X86.ShaNi.compress := NoSp.of_all (by lit_decide)
theorem compress_stack : stackUse Impl.Sha256.X86.ShaNi.compress = 0 := by lit_decide

end VG.Proof.Sha256.X86.ShaNi
