module

import VerifiedGarbage.Proof.Rc4.X86.ConstantTime
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.Rc4.X86.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Rc4.Dword
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Rc4.X86.Apply
import VerifiedGarbage.Proof.Rc4.X86.Save
import VerifiedGarbage.Proof.Rc4.X86.Lookup
public import VerifiedGarbage.Impl.Rc4.X86
public import VerifiedGarbage.Proof.MlDsa.X86.Pack.Run
public import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.X86.Replace
public import VerifiedGarbage.Spec.Rc4
public import VerifiedGarbage.Proof.Rc4.X86.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Rc4.X86.Lit
public import VerifiedGarbage.Spec.Rc4.Contract
import VerifiedGarbage.Proof.Framework.Contract

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
  have h := region_offset _ _ _ (4 * i) 4 (by omega_using [hi]) (by omega_using [hi]) hp.args
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
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have a256 : addr (s.gpr .edi) 256 = (s.gpr .edi).setWidth 64 + 256#64 := addr_of_fit (by omega_using [hfit])
  have a257 : addr (s.gpr .edi) 257 = (s.gpr .edi).setWidth 64 + 257#64 := addr_of_fit (by omega_using [hfit])
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
  have haf : InitFrame s a.mem := by
    rw [ham]
    exact (savedMem_frame _ _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact List.mem_cons_of_mem _ List.mem_cons_self
  have hasp : a.gpr .esp = s.gpr .esp := hak.gpr (by decide)
  have hb : WP isa (.block [.mov .edi (.mem (at_ .esp 12)), .mov .esi (imm 0)]) a fun b =>
      b.mem = a.mem ∧ b.rd = s.rd ∧ b.wr = s.wr ∧ b.gpr .edi = (arg s 2) ∧ b.gpr .esi = 0#32 ∧
        b.gpr .esp = s.gpr .esp := by
    have h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := hp.arg_in (i := 2) (by decide)
    have v12 : a.mem.readW (addr (s.gpr .esp) 12) 32 = (arg s 2) := hp.arg_eq haf (i := 2) (by decide)
    rrun [hasp, hak.2.1, hak.2.2, h12, v12]
  refine WP.mono hb fun b ⟨hbm, hbr, hbw, hbdi, hbsi, hbsp⟩ => ?_
  have hfit : (b.gpr .edi).toNat + 256 ≤ 2 ^ 32 := by rw [hbdi]; have := hp.ctxFit; omega_using [this]
  have hpb : InRegions b.wr ((b.gpr .edi).setWidth 64) 256 := by
    rw [hbw, hbdi]
    have h' := region_offset _ _ _ 0 256 (by decide) (by decide) hp.ctx
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h'
  have hib : IdentityInv b 0 b := ⟨by rw [identityMem_zero], rfl, rfl, rfl, rfl, hbsi⟩
  refine WP.seq (WP.mono (identity_loop b b (by decide) hfit hpb hib) fun c hc => ?_)
  obtain ⟨hcm, hcr, hcw, hcdi, hcsp, _⟩ := hc
  have hreset : WP isa (.block [.mov .esi (imm 0), .mov .ebx (imm 0), .mov .ebp (imm 0)]) c
      fun d => d.mem = c.mem ∧ d.rd = c.rd ∧ d.wr = c.wr ∧ d.gpr .edi = c.gpr .edi ∧
        d.gpr .esp = c.gpr .esp ∧ d.gpr .esi = 0#32 ∧ d.gpr .ebx = 0#32 ∧ d.gpr .ebp = 0#32 := by
    rrun
  refine WP.seq (WP.mono hreset fun d hd => ?_)
  obtain ⟨hdm, hdr, hdw, hddi, hdsp, hdsi, hdbx, hdbp⟩ := hd
  have hdf : InitFrame s d.mem := by
    rw [hdm, hcm, hbm, hbdi]
    exact haf.table (identityMem_frame _ _ _ (by decide))
  have hdC : d.gpr .edi = (arg s 2) := by rw [hddi, hcdi, hbdi]
  have hdS : d.gpr .esp = s.gpr .esp := by rw [hdsp, hcsp, hbsp]
  have hdrd : d.rd = s.rd := by rw [hdr, hcr, hbr]
  have hdwr : d.wr = s.wr := by rw [hdw, hcw, hbw]
  have hkey : keyOf d.mem (arg s 0) (arg s 1) = bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat := by
    unfold keyOf bytesAt
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    exact hdf _ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.keyCtx _ (Offset.contains_base _ (by omega_using [hk']) (by omega_using [hk']))
      · exact hp.keyScratch _ (Offset.contains_base _ (by omega_using [hk']) (by omega_using [hk']))
  have hpre : SchedulePre d (arg s 0) (arg s 1) := by
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
  have hid : ScheduleInv d (arg s 0) (arg s 1) 0 d := by
    refine ⟨TableFrame.refl _ _, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · rw [hdm, hcm, hddi, hcdi, identityMem_table, schedule_zero]
    · rw [hdbp]; rfl
    · rw [hdsi]
    · rw [hdbx, Nat.zero_mod]
  refine WP.seq (WP.mono (schedule_loop d d _ _ (by decide) hpre hid) fun e he => ?_)
  have heC : e.gpr .edi = arg s 2 := by rw [he.p, hdC]
  have heS : e.gpr .esp = s.gpr .esp := by rw [he.sp, hdS]
  have herd : e.rd = s.rd := by rw [he.rd, hdrd]
  have hewr : e.wr = s.wr := by rw [he.wr, hdwr]
  rw [WP.block_append_iff]
  refine WP.mono (init_finish e (by rw [heC]; exact hp.ctxFit) (by rw [hewr, heC]; exact hp.ctx))
    fun f ⟨fax, fm, fk⟩ => ?_
  have hfS : f.gpr .esp = s.gpr .esp := (fk.gpr (by decide)).trans heS
  have hfrd : f.rd = s.rd := fk.2.1.trans herd
  have hfwr : f.wr = s.wr := fk.2.2.trans hewr
  have hctxf : Frame [⟨(arg s 2).setWidth 64, 258⟩] a.mem f.mem := by
    rw [fm, heC]
    refine frame_finish ?_ _ _
    have h1 := frame_of_table he.frame
    have h0 := frame_of_table (identityMem_frame a.mem ((arg s 2).setWidth 64) 256 (by decide))
    rw [hdm, hcm, hbm, hdC] at h1
    rw [hbdi] at h1
    exact h0.trans h1
  have hsaved : Saved f.mem (arg s 3) s := by
    have h0 := saved_savedMem s.mem (arg s 3) s
    rw [← ham] at h0
    refine h0.frame hctxf ?_
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact fun x h₁ h₂ => hp.ctxScratch x h₂ (by simp only [Region.Contains] at h₁ ⊢; omega_using [h₁])
  have hff : InitFrame s f.mem := by
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
  have ha : ∀ i, arg t i = arg s i := fun i => by unfold arg argAddr; rw [hm, hsp]
  have hA : argAddr t 0 = argAddr s 0 := by unfold argAddr; rw [hsp]
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
  have h8 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := hp.arg_in (i := 1) (by decide)
  have hcheck : WP isa (.block [.mov .eax (.mem (at_ .esp 8)), .alu .sub .eax (imm 1),
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
  have htp : InitPre t := hp.transport htm (htk.gpr (by decide)) htr htw
  have ha : ∀ i, arg t i = arg s i := fun i => by
    unfold arg argAddr; rw [htm, htk.gpr (r := .esp) (by decide)]
  let good := 1 ≤ (arg s 1).toNat ∧ (arg s 1).toNat ≤ 256
  have hcond : isa.eval .ae t = some (decide (¬ good)) := by
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
  have hp : InitPre s :=
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
  have hp := applyPre_of hs
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
  have narrowSat : ∃ s, initC.pre s := by
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
  have narrowSat : ∃ s, applyC.pre s := by
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
allocates it and copies their three argument slots, and zero it after the
code (`Verified.stackScratchWiped`): 84 bytes, 64 of working space. The code
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
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.init)
      (Spec.Rc4.initContract X86.abi 84) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc4.initSig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.initPost X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 84)
    init_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.initPost_local _)
    (Proof.Rc4.initPostOut_local _) initFrameSat_pre

theorem apply_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 84 3 16 Impl.Rc4.X86.apply)
      (Spec.Rc4.applyContract X86.abi 84) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc4.applySig) (nm := "scratch") (e := .u64) (n := 8)
    (post := Spec.Rc4.applyPost X86.abi.ptrBits) (wa := true) (stack := 0) (bytes := 84)
    (leak := some (Spec.Rc4.applyLeak X86.abi.ptrBits))
    apply_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Rc4.applyPost_local _)
    (Proof.Rc4.applyPostOut_local _) applyFrameSat_pre (hleak := Proof.Rc4.applyLeak_local _)

end VG.Proof.Rc4.X86
