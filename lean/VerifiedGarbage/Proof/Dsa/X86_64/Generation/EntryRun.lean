module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryResult
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc

/-! # Complete native execution restores both frames and all saved registers -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64


variable {checkName : String}

theorem entryInner_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {s u : State} (h : GenerationABI s)
    (hg : u.gpr = (allocState 48 s).gpr) (hr : u.rd = s.rd)
    (hw : u.wr = (allocState 48 s).wr)
    (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem)
    (saved : Saved u.mem (savedBase s) s.gpr spillSlots) :
    WP isa (.frame (.alloc 296)
      (Impl.Dsa.X86_64.Generation.entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) (.free 296)) u fun t =>
      EntryResult s t ∧ Saved t.mem (savedBase s) s.gpr spillSlots ∧
      t.gpr .rsp = u.gpr .rsp ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  apply alloc_frame_ok (by decide) (outer_stack_room h hg)
  apply WP.mono (entryBody_abi (checkName := checkName) H M Sq T h hg hr hw hf saved)
  intro t ⟨result, saved, sp, rd, wr⟩
  exact ⟨sp, wr, result.free 296, saved, freeState_rsp sp, rd, freeState_wr wr⟩

theorem entryRun_ok (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {s : State} (h : GenerationABI s) :
    WP isa (Impl.Dsa.X86_64.Generation.code (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) s fun t =>
      EntryResult s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold Impl.Dsa.X86_64.Generation.code
  apply alloc_frame_ok (by decide) (by have hl := h.stackLower; omega)
  refine WP.seq (WP.mono (entrySave_ok (s := allocState 48 s) (List.mem_cons_self ..)) ?_)
  intro u ⟨hg, hr, hw, saved, hf⟩
  have saved' : Saved u.mem (savedBase s) s.gpr spillSlots := by
    intro p hp
    have hh := saved p hp
    change u.mem.readW (Spill.slot (savedBase s) p.2) 64 = (allocState 48 s).gpr p.1 at hh
    change u.mem.readW _ 64 = _
    rw [hh]
    have hn : p.1 ≠ .rsp := by
      simp only [spillSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [allocState, State.setReg, hn]
  refine WP.seq (WP.mono (entryInner_ok (checkName := checkName) H M Sq T h hg hr hw hf saved') ?_)
  intro v ⟨result, sv, spv, rdv, wrv⟩
  have vsp : v.gpr .rsp = savedBase s := by rw [spv, hg]; rfl
  have vwr : (⟨v.gpr .rsp, 48⟩ : Region) ∈ v.wr := by
    rw [vsp, wrv, hw]
    exact List.mem_cons_self ..
  apply WP.mono (entryRestore_ok s.gpr vwr (by rw [vsp]; exact sv))
  intro t ⟨restore, rax, sp, mem, rd, wr⟩
  have tsp : t.gpr .rsp = (allocState 48 s).gpr .rsp := by rw [sp, spv, hg]
  have twr : t.wr = (allocState 48 s).wr := wr.trans (wrv.trans hw)
  refine ⟨tsp, twr, (result.congr rax mem).free 48, ?_, rd.trans (rdv.trans hr), freeState_wr twr⟩
  intro r hr
  by_cases hs : r = .rsp
  · subst r; exact freeState_rsp tsp
  · have hin : r ∈ spillSlots.map Prod.fst := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact False.elim (hs rfl) | decide
    have he := restore r hin
    simpa only [freeState, State.setReg, hs, ↓reduceIte] using he

end VG.Proof.Dsa.X86_64.Generation
