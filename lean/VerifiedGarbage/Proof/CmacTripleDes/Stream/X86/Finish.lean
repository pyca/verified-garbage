module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Common
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Inline
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Common
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Inline
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.TripleDes.SboxTables

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_finish`

The code saves the registers, copies the chaining value to `out`, computes
the number of bytes held back, and runs `finalize` with the state as its key
and `out` as its state: its result is the MAC of the message the state
represents (`repr_finish`). The code before the run is constant time by the
taint analysis, and the run by `finalize`'s own proof (`fin_rel`), its
arguments pinned by `HMid`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86

open VG.WriteBytes

open VG.Impl.CmacTripleDes.X86 (at_)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.CmacTripleDes.X86 (ciphAt)
open VG.Proof.CmacTripleDes.Stream (held held_le)

section
variable (s₀ : State)

abbrev hSt : BitVec 32 := arg s₀ 0
abbrev hO : BitVec 32 := arg s₀ 3
abbrev hSc : BitVec 32 := arg s₀ 4
abbrev hE : BitVec 32 := s₀.gpr .esp
abbrev hstR : Region := ⟨(hSt s₀).setWidth 64, 416⟩
abbrev hoR : Region := ⟨(hO s₀).setWidth 64, 8⟩
abbrev hscR : Region := ⟨(hSc s₀).setWidth 64, 688⟩
abbrev haR : Region := ⟨argAddr s₀ 0, 20⟩
/-- The bytes held back. -/
abbrev hH : Nat := held (countX86 s₀).toNat

/-- Where the function writes: the state, `out`, the scratch buffer and the stack. -/
abbrev HBig : List Region := [hstR s₀, hoR s₀, hscR s₀, below (hE s₀) 24]

end

/-- The precondition, by name. -/
structure HPre (s₀ : State) : Prop where
  rd : s₀.rd = [haR s₀]
  wr : s₀.wr = [hstR s₀, hoR s₀, hscR s₀]
  st_o : (hstR s₀).Disjoint (hoR s₀)
  st_s : (hstR s₀).Disjoint (hscR s₀)
  o_s : (hoR s₀).Disjoint (hscR s₀)
  a_st : (haR s₀).Disjoint (hstR s₀)
  a_o : (haR s₀).Disjoint (hoR s₀)
  a_s : (haR s₀).Disjoint (hscR s₀)
  ret_st : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hstR s₀)
  ret_o : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hoR s₀)
  ret_s : (⟨(hE s₀).setWidth 64, 4⟩ : Region).Disjoint (hscR s₀)
  b_st' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (hstR s₀)
  b_o' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (hoR s₀)
  b_s' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 24, 24⟩ : Region).Disjoint (hscR s₀)
  fSt : (hSt s₀).toNat + 416 ≤ 2 ^ 32
  fO : (hO s₀).toNat + 8 ≤ 2 ^ 32
  fS : (hSc s₀).toNat + 688 ≤ 2 ^ 32
  esp24 : 24 ≤ (hE s₀).toNat
  espfit : (hE s₀).toNat + 24 ≤ 2 ^ 32

theorem HPre.of {s₀ : State} (h : finishX86.pre s₀) : HPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t⟩

namespace HPre
variable {s₀ : State} (hp : HPre s₀)
include hp

theorem b_st : (below (hE s₀) 24).Disjoint (hstR s₀) := by rw [below_eq hp.esp24]; exact hp.b_st'
theorem b_o : (below (hE s₀) 24).Disjoint (hoR s₀) := by rw [below_eq hp.esp24]; exact hp.b_o'
theorem b_s : (below (hE s₀) 24).Disjoint (hscR s₀) := by rw [below_eq hp.esp24]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 5 ≤ 2 ^ 32 := by have := hp.espfit; omega_arith

theorem arg_in {i : Nat} (hi : i < 5) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨haR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `HBig` changes. -/
theorem keep {m : Mem} (hf : Frame (HBig s₀) s₀.mem m) {i : Nat} (hi : i < 5) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_o.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp24).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 5 s₀ := by
  refine ⟨by have := hp.espfit; omega_arith, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.espfit; omega_arith) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.espfit; omega_arith) hp.ret_o hp.a_o
  · exact VG.X86.Taint.frame_disjoint (n := 20) (by have := hp.espfit; omega_arith) hp.ret_s hp.a_s

end HPre

theorem HPre.savedMem_big {s₀ : State} (_hp : HPre s₀) : Frame (HBig s₀) s₀.mem (savedMem s₀ (hSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨hscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before `finalize` -/

theorem finSave_eq : finSave = .mov .eax (.mem (argOp 4)) :: (save ++ ([.mov .esi (.mem (argOp 0)),
    .alu .add .esi (.imm 400), .mov .edi (.mem (argOp 3)), .mov .ecx (.imm 8)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure HS₁ (s₀ s : State) : Prop where
  esi : s.gpr .esi = hSt s₀ + BitVec.ofNat 32 400
  edi : s.gpr .edi = hO s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 8
  esp : s.gpr .esp = hE s₀
  mem : s.mem = savedMem s₀ (hSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : HPre s₀) : WP isa (.block finSave) s₀ (HS₁ s₀) := by
  have fS : (arg s₀ 4).toNat + 688 ≤ 2 ^ 32 := hp.fS
  rw [finSave_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := hSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  have hm₂ : s₂.mem = savedMem s₀ (hSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂, u₁.other _ (by decide)]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  have av : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 0 (by decide))
    fun s₃ u₃ => wp_addi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₅ u₅ => wp_movi fun s₆ u₆ => WP.block_nil ?_
  exact ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.gpr], u₆.gpr,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂],
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂'],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']⟩

/-- The memory after the saves and the copy of the chaining value. -/
def hMem (s₀ : State) : Mem :=
  writeBytes (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
    (Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8)

theorem hMem_out (s₀ : State) : Frame [hoR s₀] (savedMem s₀ (hSc s₀)) (hMem s₀) :=
  writeBytes_frame _ _ _ (R := hoR s₀) (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)

theorem hMem_frame {s₀ : State} (hp : HPre s₀) : Frame (HBig s₀) s₀.mem (hMem s₀) :=
  hp.savedMem_big.trans ((hMem_out s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, fun _ h => h⟩)

/-- What the code before `finalize` leaves. -/
structure HMid (s₀ s : State) : Prop where
  args : FArgs s (hSt s₀) (hO s₀) (hSt s₀ + BitVec.ofNat 32 408) (hSc s₀) (hH s₀)
  esp : s.gpr .esp = hE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = hMem s₀

theorem finPre_wp {s₀ : State} (hp : HPre s₀) : WP isa finPre s₀ (HMid s₀) := by
  have fS : (arg s₀ 4).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fO : (arg s₀ 3).toNat + 8 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (hSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (hO s₀).toNat + 8 ≤ 2 ^ 32 := hp.fO
  have fS₂ : (hSc s₀).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have e24 := hp.esp24
  unfold finPre
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  have p400 : ((hSt s₀ + BitVec.ofNat 32 400).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 400 :=
    add_setWidth (by omega_arith)
  have c400 : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 400).setWidth 64, 8⟩ (hstR s₀) := by
    rw [p400]; exact Offset.sub_base _ (by decide)
  refine WP.seq (WP.mono (copy_wp (L := 8) (by decide) h₁.esi h₁.edi h₁.ecx
    (fun _ => by rw [add_toNat (by omega_arith)]; omega_arith) (fun _ => by omega_arith)
    (fun _ => by
      rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨hstR s₀, by simp, 400, p400, by simp⟩)
    (fun _ => by
      rw [h₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩)
    (fun _ => hp.st_o.sub_left c400)) fun s₂ h₂ => ?_)
  obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
  have hm₂ : s₂.mem = hMem s₀ := by rw [m₂, h₁.mem, p400]; rfl
  have esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h₁.esp]
  have rd₂' : s₂.rd = s₀.rd := by rw [rd₂, h₁.rd]
  have wr₂' : s₂.wr = s₀.wr := by rw [wr₂, h₁.wr]
  have av : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep (hMem_frame hp) hi
  refine WP.seq (held_ok (r := .esi) (by decide) (by decide) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 1 (by decide)) (av 2 (by decide))
    fun s₃ esi₃ g₃ m₃ rd₃ wr₃ => ?_)
  have esp₃ : s₃.gpr .esp = hE s₀ := by rw [g₃ _ (by decide) (by decide), esp₂]
  have rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [rd₃, wr₃, rd₂', wr₂']
  have av₃ : ∀ i < 5, s₃.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by rw [m₃]; exact av i hi
  unfold finArgs
  refine wp_arg (s₀ := s₀) esp₃ (by rw [rw₃]; exact hp.arg_in (by decide)) (av₃ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide)) (by rw [u₄.mem]; exact av₃ 3 (by decide))
    fun s₅ u₅ => wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact av₃ 4 (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have esp₈ : s₈.gpr .esp = hE s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), esp₃]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂']
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂']
  have m₈ : s₈.mem = hMem s₀ := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, hm₂]
  have hh : hH s₀ ≤ 8 := held_le (countX86 s₀).toNat
  have p408 : ((hSt s₀ + BitVec.ofNat 32 408).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 408 :=
    add_setWidth (by omega_arith)
  have cP : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 408).setWidth 64, hH s₀⟩ (hstR s₀) := by
    rw [p408]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨?_, esp₈, rd₈, wr₈, m₈⟩
  exact
  { eax := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    edx := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
    ebx := by rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr]; rfl
    esi := by
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), esi₃]
    edi := u₈.gpr
    len := hh
    esp := by rw [esp₈]; exact e24
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left cP
    ps := (hp.st_s.sub_left cP).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₈]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bP := by rw [esp₈]; exact hp.b_st.sub_right cP
    bSt := by rw [esp₈]; exact hp.b_o
    bS := by rw [esp₈]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fK := by omega_arith
    fSt := fO
    fP := by rw [add_toNat (by omega_arith)]; omega_arith
    fS := by omega_arith
    reads := by
      rw [rd₈, wr₈, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hstR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hstR s₀, by simp, 408, p408, by simp; omega_arith⟩
    writes := by
      rw [wr₈, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishX86.pre s₀) :
    WP isa finish s₀ fun s' => abiPreserved s₀ s' ∧ finishX86.post s₀ s' := by
  have hp := HPre.of h0
  have fS : (arg s₀ 4).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fSt₂ : (hSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fS₂ : (hSc s₀).toNat + 688 ≤ 2 ^ 32 := hp.fS
  have e24 := hp.esp24
  unfold finish
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_)
  have f₂ : Frame [hoR s₀, ⟨(hSc s₀).setWidth 64, 640⟩, below (hE s₀) 24] s₁.mem s₂.mem := by
    have := h₂.frame; rw [h₁.esp] at this; exact this
  have F₂ : Frame (HBig s₀) s₀.mem s₂.mem := (h₁.mem ▸ hMem_frame hp).trans (f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  -- The saved registers.
  have slots : ∀ r d, (r, d) ∈ saved →
      s₂.mem.readW ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    have hb := saved_bound _ hrd
    have sub : Region.Sub ⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (hscR s₀) := Offset.sub_base _ (by omega_arith)
    have c := Region.contains_self ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₂.readW c (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hp.o_s.symm.sub_left sub
        · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
        · exact hp.b_s.symm.sub_left sub) (by decide),
      h₁.mem, (hMem_out s₀).readW c (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact hp.o_s.symm.sub_left sub) (by decide)]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (restore_wp (s₀ := s₀) (i := 4) (Sc := hSc s₀)
    (by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp])
    (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hp.arg_in (by decide)) (hp.keep F₂ (by decide)) fS (by
      rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₃ ⟨hcs, m₃⟩ => ?_
  refine ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [m₃]
    refine F₂.readW (r := ⟨(hE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_o
    · exact hp.ret_s
    · exact ret_below e24
  · intro key msg hr hc hlen
    show Spec.Aes.bytesAt s₃.mem ((hO s₀).setWidth 64) 8 = _
    rw [m₃]
    have hn : (countX86 s₀).toNat = msg.length := by
      rw [hc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen
    -- The state, unchanged before `finalize`.
    have F₁ : Frame [⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 640, 16⟩, hoR s₀] s₀.mem s₁.mem := by
      rw [h₁.mem]
      exact ((savedMem_frame _ _).mono (by simp)).trans ((hMem_out s₀).mono (by simp))
    have hr₁ : Spec.Cmac.tdesRepr s₁.mem ((hSt s₀).setWidth 64) key msg :=
      Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => F₁.bytes (R := hstR s₀) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.st_s.sub_right (Offset.sub_base _ (by decide))
        · exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
    obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
    rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
    obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
    have hciph : ciphAt s₁.mem ((hSt s₀).setWidth 64) = Spec.Cmac.tdes key := by
      simp only [ciphAt, hks, Spec.Cmac.tdes]
    have e₂ : Spec.Aes.bytesAt s₁.mem ((hO s₀).setWidth 64) 8 =
        Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64 + 400) 8 := by
      rw [show (hSt s₀).setWidth 64 + 400 = (hSt s₀).setWidth 64 + BitVec.ofNat 64 400 from rfl, h₁.mem,
        Proof.Cmac.bytesAt_frame (hMem_out s₀) (p := (hSt s₀).setWidth 64 + BitVec.ofNat 64 400) (n := 8)
          (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_o.sub_left (Offset.sub_base _ (by decide))) (by decide), hMem]
      have := bytesAt_writeBytes_self (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
        (xs := Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 400) 8)
        (by rw [Proof.Cmac.bytesAt_length]; decide)
      rw [Proof.Cmac.bytesAt_length] at this
      exact this
    have out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hH, hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, add_setWidth (by omega_arith), hH, hn,
      show (hSt s₀).setWidth 64 + BitVec.ofNat 64 408 = (hSt s₀).setWidth 64 + 408 from rfl, happ,
      Proof.CmacTripleDes.Stream.tdesCmac_eq]

/-! ## Constant time -/

/-- What `finalize` leaves. -/
structure HAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = hE s₀
  wr : s.wr = s₀.wr
  frame : Frame (HBig s₀) s₀.mem s.mem

theorem fin_after {s₀ s : State} (hp : HPre s₀) (h : HMid s₀ s) : WP isa finFrame s (HAft s₀) :=
  WP.mono (fin_wp h.args) fun s' h' => by
    have fr := h'.frame
    rw [h.esp] at fr
    refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.wr, h.wr],
      (h.mem ▸ hMem_frame hp).trans (fr.sub fun r hr => ?_)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem finish_rel {s₀ s₀' : State} (h0 : finishX86.pre s₀) (h0' : finishX86.pre s₀')
    (hq : finishX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  have hp := HPre.of h0
  have hp' := HPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : hSt s₀ = hSt s₀' := qa 0 (by decide)
  have eH : hH s₀ = hH s₀' := by rw [hH, hH, countX86, countX86, qa 1 (by decide), qa 2 (by decide)]
  have e3 : hO s₀ = hO s₀' := qa 3 (by decide)
  have e4 : hSc s₀ = hSc s₀' := qa 4 (by decide)
  have ag : ∀ {a b : State}, Pt 5 s₀ a → Pt 5 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 5)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 5))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := finPre) (by taint_decide)).wp (F₁ := HMid s₀) (F₂ := HMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c := ((fin_rel (E := hE s₀) (Q := fun a b => HMid s₀ a ∧ HMid s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, eH, e3, e4]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := HAft s₀) (F₂ := HAft s₀') fun _ _ h => ⟨fin_after hp h.1, fin_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have b := RelCT.taint (A := taint) (P := fun a b => HAft s₀ a ∧ HAft s₀' b) (argTaint [] (4 + 4 * 5))
    (fun _ _ h => ag ⟨h.1.esp, h.1.wr, fun _ hi => hp.keep h.1.frame hi⟩
      ⟨h.2.esp, h.2.wr, fun _ hi => hp'.keep h.2.frame hi⟩) (c := .block (restore 4)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finish_ct : ConstantTime isa finishX86.pre finishX86.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.X86
