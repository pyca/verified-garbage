module

public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
public import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86.Absorb
meta import VerifiedGarbage.Proof.CmacAes.Stream.Scratch
meta import VerifiedGarbage.Proof.CmacAes.X86.Verified
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Common
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86.Common
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Call
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86.Call
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `CmacAes.Stream.X86.Verified`, which only this module used -/

section

/-! ### `CmacAes.Stream.X86.Finish`, which only this module used -/

section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_finish`

The code saves the registers, copies the chaining value to `out`, computes the
number of bytes held back, and calls `vg_cmac_aes_finalize` with the state as
its key and `out` as its state: its result is the MAC of the message the state
represents (`repr_finish`). The code before the call is constant time by the
taint analysis, and the call by its own proof (`fin_rel`), its arguments
pinned by `HMid`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi)
open VG.Proof.CmacAes.X86 (wp_arg toNat_rounds)
open VG.Proof.Cmac.Stream (held held_le)

section
variable (s₀ : State)

abbrev hSt : BitVec 32 := arg s₀ 0
abbrev hR : Nat := (arg s₀ 1).toNat
abbrev hO : BitVec 32 := arg s₀ 4
abbrev hSc : BitVec 32 := arg s₀ 5
abbrev hE : BitVec 32 := s₀.gpr .esp
abbrev hstR : Region := ⟨(hSt s₀).setWidth 64, 304⟩
abbrev hoR : Region := ⟨(hO s₀).setWidth 64, 16⟩
abbrev hscR : Region := ⟨(hSc s₀).setWidth 64, 2304⟩
abbrev haR : Region := ⟨argAddr s₀ 0, 24⟩
/-- The bytes held back. -/
abbrev hH : Nat := held (countX86 s₀).toNat

/-- Where the function writes: the state, `out`, the scratch buffer and the stack. -/
abbrev HBig : List Region := [hstR s₀, hoR s₀, hscR s₀, below (hE s₀) 60]

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
  b_st' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 60, 60⟩ : Region).Disjoint (hstR s₀)
  b_o' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 60, 60⟩ : Region).Disjoint (hoR s₀)
  b_s' : (⟨(hE s₀).setWidth 64 - BitVec.ofNat 64 60, 60⟩ : Region).Disjoint (hscR s₀)
  fSt : (hSt s₀).toNat + 304 ≤ 2 ^ 32
  fO : (hO s₀).toNat + 16 ≤ 2 ^ 32
  fS : (hSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp60 : 60 ≤ (hE s₀).toNat
  espfit : (hE s₀).toNat + 28 ≤ 2 ^ 32
  rounds : hR s₀ = 10 ∨ hR s₀ = 12 ∨ hR s₀ = 14

theorem HPre.of {s₀ : State} (h : finishX86.pre s₀) : HPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u⟩

namespace HPre
variable {s₀ : State} (hp : HPre s₀)
include hp

theorem b_st : (below (hE s₀) 60).Disjoint (hstR s₀) := by rw [below_eq hp.esp60]; exact hp.b_st'
theorem b_o : (below (hE s₀) 60).Disjoint (hoR s₀) := by rw [below_eq hp.esp60]; exact hp.b_o'
theorem b_s : (below (hE s₀) 60).Disjoint (hscR s₀) := by rw [below_eq hp.esp60]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 6 ≤ 2 ^ 32 := by have := hp.espfit; omega_arith

theorem arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨haR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `HBig` changes. -/
theorem keep {m : Mem} (hf : Frame (HBig s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_o.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp60).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 6 s₀ := by
  refine ⟨by have := hp.espfit; omega_arith, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega_arith) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega_arith) hp.ret_o hp.a_o
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by have := hp.espfit; omega_arith) hp.ret_s hp.a_s

end HPre

theorem HPre.savedMem_big {s₀ : State} (_hp : HPre s₀) : Frame (HBig s₀) s₀.mem (savedMem s₀ (hSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨hscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before the call -/

theorem finSave_eq : finSave = .mov .eax (argOp 5) :: (save ++ ([.mov .esi (argOp 0), .alu .add .esi (.imm 272),
    .mov .edi (argOp 4), .mov .ecx (.imm 16)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure HS₁ (s₀ s : State) : Prop where
  esi : s.gpr .esi = hSt s₀ + BitVec.ofNat 32 272
  edi : s.gpr .edi = hO s₀
  ecx : s.gpr .ecx = BitVec.ofNat 32 16
  esp : s.gpr .esp = hE s₀
  mem : s.mem = savedMem s₀ (hSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : HPre s₀) : WP isa (.block finSave) s₀ (HS₁ s₀) := by
  have fS : (arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  rw [finSave_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := hSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  obtain hm₂ : s₂.mem = savedMem s₀ (hSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂, u₁.other _ (by decide)]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  obtain av : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 0 (by decide))
    fun s₃ u₃ => wp_addi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 4 (by decide)) fun s₅ u₅ => wp_movi fun s₆ u₆ => WP.block_nil ?_
  exact ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.gpr], u₆.gpr,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂],
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂'],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']⟩

/-- The memory after the saves and the copy of the chaining value. -/
def hMem (s₀ : State) : Mem :=
  writeBytes (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
    (Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16)

theorem hMem_frame {s₀ : State} (hp : HPre s₀) : Frame (HBig s₀) s₀.mem (hMem s₀) :=
  hp.savedMem_big.trans ((writeBytes_frame _ _ _ (by
    rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, fun _ h => h⟩)

/-- What the code before the call leaves. -/
structure HMid (s₀ s : State) : Prop where
  args : FArgs s (hSt s₀) (hO s₀) (hSt s₀ + BitVec.ofNat 32 288) (hSc s₀) (hH s₀) (hR s₀)
  esp : s.gpr .esp = hE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = hMem s₀

theorem finPre_wp {s₀ : State} (hp : HPre s₀) : WP isa finPre s₀ (HMid s₀) := by
  have fS : (arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO : (arg s₀ 4).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (hSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (hO s₀).toNat + 16 ≤ 2 ^ 32 := hp.fO
  obtain hh₂ : hH s₀ ≤ 16 := held_le _
  have fS₂ : (hSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e60 := hp.esp60
  unfold finPre
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  obtain p272 : ((hSt s₀ + BitVec.ofNat 32 272).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 272 :=
    add_setWidth (by omega_arith)
  obtain c272 : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 272).setWidth 64, 16⟩ (hstR s₀) := by
    rw [p272]; exact Offset.sub_base _ (by decide)
  refine WP.seq (WP.mono (copy_wp (L := 16) (by decide) h₁.esi h₁.edi h₁.ecx
    (fun _ => by rw [add_toNat (by omega_arith)]; omega_arith) (fun _ => by omega_arith)
    (fun _ => by
      rw [h₁.rd, h₁.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨hstR s₀, by simp, 272, p272, by simp⟩)
    (fun _ => by
      rw [h₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩)
    (fun _ => hp.st_o.sub_left c272)) fun s₂ h₂ => ?_)
  obtain ⟨m₂, g₂, rd₂, wr₂⟩ := h₂
  obtain hm₂ : s₂.mem = hMem s₀ := by rw [m₂, h₁.mem, p272]; rfl
  obtain esp₂ : s₂.gpr .esp = hE s₀ := by rw [g₂ _ (by decide) (by decide) (by decide) (by decide), h₁.esp]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, h₁.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, h₁.wr]
  obtain av : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep (hMem_frame hp) hi
  refine WP.seq (held_ok (r := .esi) (by decide) (by decide) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 2 (by decide)) (av 3 (by decide))
    fun s₃ esi₃ g₃ m₃ rd₃ wr₃ => ?_)
  obtain esp₃ : s₃.gpr .esp = hE s₀ := by rw [g₃ _ (by decide) (by decide), esp₂]
  obtain rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [rd₃, wr₃, rd₂', wr₂']
  obtain av₃ : ∀ i < 6, s₃.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by rw [m₃]; exact av i hi
  unfold finArgs
  refine wp_arg (s₀ := s₀) esp₃ (by rw [rw₃]; exact hp.arg_in (by decide)) (av₃ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide)) (by rw [u₄.mem]; exact av₃ 1 (by decide))
    fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem]; exact av₃ 4 (by decide)) fun s₆ u₆ => wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), esp₃])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact av₃ 5 (by decide)) fun s₉ u₉ => WP.block_nil ?_
  obtain esp₉ : s₉.gpr .esp = hE s₀ := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esp₃]
  obtain rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, rd₂']
  obtain wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, wr₂']
  obtain m₉ : s₉.mem = hMem s₀ := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, hm₂]
  obtain hh := held_le (countX86 s₀).toNat
  obtain p288 : ((hSt s₀ + BitVec.ofNat 32 288).setWidth 64) = (hSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
    add_setWidth (by omega_arith)
  obtain cP : Region.Sub ⟨(hSt s₀ + BitVec.ofNat 32 288).setWidth 64, hH s₀⟩ (hstR s₀) := by
    rw [p288]; exact Offset.sub_base _ (by omega_arith)
  refine ⟨?_, esp₉, rd₉, wr₉, m₉⟩
  exact
  { eax := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr]
    ecx := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr]; exact arg_ofNat s₀ 1
    edx := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
    ebx := by
      rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl
    esi := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
    edi := u₉.gpr
    rounds := hp.rounds
    len := hh
    esp := by rw [esp₉]; exact e60
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left cP
    ps := (hp.st_s.sub_left cP).sub_right (Region.sub_prefix (by decide))
    sts := hp.o_s.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₉]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bP := by rw [esp₉]; exact hp.b_st.sub_right cP
    bSt := by rw [esp₉]; exact hp.b_o
    bS := by rw [esp₉]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fK := by omega_arith
    fSt := fO
    fP := by rw [add_toNat (by omega_arith)]; omega_arith
    fS := by omega_arith
    reads := by
      rw [rd₉, wr₉, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hstR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hstR s₀, by simp, 288, p288, by simp; omega_arith⟩
    writes := by
      rw [wr₉, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hoR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨hscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishX86.pre s₀) :
    WP isa (finish v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ finishX86.post s₀ s' := by
  obtain hp := HPre.of h0
  have fS : (arg s₀ 5).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO : (arg s₀ 4).toNat + 16 ≤ 2 ^ 32 := hp.fO
  have fSt₂ : (hSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fO₂ : (hO s₀).toNat + 16 ≤ 2 ^ 32 := hp.fO
  obtain hh₂ : hH s₀ ≤ 16 := held_le _
  have fS₂ : (hSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e60 := hp.esp60
  unfold finish
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono ((fin_call v) h₁.args) fun s₂ h₂ => ?_)
  obtain f₂ : Frame [hoR s₀, ⟨(hSc s₀).setWidth 64, 2176⟩, below (hE s₀) 60] s₁.mem s₂.mem := by
    have := h₂.frame; rw [h₁.esp] at this; exact this
  obtain F₂ : Frame (HBig s₀) s₀.mem s₂.mem := (h₁.mem ▸ hMem_frame hp).trans (f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hoR s₀, by simp, fun _ h => h⟩
    · exact ⟨hscR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩)
  -- The saved registers.
  obtain slots : ∀ r d, (r, d) ∈ saved →
      s₂.mem.readW ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    obtain hb := saved_bound _ hrd
    obtain sub : Region.Sub ⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (hscR s₀) := Offset.sub_base _ (by omega_arith)
    obtain c := Region.contains_self ((hSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₂.readW c (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl
        · exact hp.o_s.symm.sub_left sub
        · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
        · exact hp.b_s.symm.sub_left sub) (by decide),
      h₁.mem, hMem, (writeBytes_frame _ _ _ (R := hoR s₀) (by
        rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).readW c (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq; exact hp.o_s.symm.sub_left sub) (by decide)]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (restore_wp (s₀ := s₀) (i := 5) (Sc := hSc s₀) (by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp])
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
    · exact ret_below e60
  · intro key msg hr hRk hc hlen
    show Spec.Aes.bytesAt s₃.mem ((hO s₀).setWidth 64) 16 = _
    rw [m₃]
    obtain hn : (countX86 s₀).toNat = msg.length := by
      rw [hc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlen
    -- The state, unchanged before the call.
    obtain F₁ : Frame [⟨(hSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩, hoR s₀] s₀.mem s₁.mem := by
      rw [h₁.mem, hMem]
      exact ((savedMem_frame _ _).mono (by simp)).trans ((writeBytes_frame _ _ _ (R := hoR s₀) (by
        rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)).mono (by simp))
    obtain fSt' : ∀ {d n : Nat}, d + n ≤ 304 →
        Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64 + BitVec.ofNat 64 d) n =
          Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun {d n} hd => by
      refine Proof.Cmac.bytesAt_frame F₁ (fun r hr => ?_) (by omega_arith)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ (by decide))
      · exact hp.st_o.sub_left (Offset.sub_base _ hd)
    obtain k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    obtain ⟨⟨hkl, hks, hsk⟩, hcv, hhb⟩ := (Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr
    have hR' : hR s₀ = Spec.Aes.rounds (key.length / 4) := hRk
    obtain hRb : 16 * (hR s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_arith
    obtain hsch : Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64) (16 * (hR s₀ + 1)) = Spec.Aes.expandKey key := by
      have := fSt' (d := 0) (n := 16 * (hR s₀ + 1)) (by omega_arith)
      rw [k0] at this; rw [this, hR']; exact hks
    obtain hciph : Spec.Cmac.aesWith (hR s₀) (Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64) (16 * (hR s₀ + 1))) =
        Spec.Cmac.aes key := by rw [hsch, hR']; rfl
    obtain e₁ : Spec.Aes.bytesAt s₁.mem ((hSt s₀).setWidth 64 + 240) 32 =
        Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + 240) 32 := fSt' (d := 240) (by decide)
    obtain e₂ : Spec.Aes.bytesAt s₁.mem ((hO s₀).setWidth 64) 16 =
        Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + 272) 16 := by
      rw [h₁.mem, hMem]
      have := bytesAt_writeBytes_self (savedMem s₀ (hSc s₀)) ((hO s₀).setWidth 64)
        (xs := Spec.Aes.bytesAt (savedMem s₀ (hSc s₀)) ((hSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16)
        (by rw [Proof.Cmac.bytesAt_length]; decide)
      rw [Proof.Cmac.bytesAt_length] at this
      rw [this]
      exact Proof.Cmac.bytesAt_frame (savedMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)
    obtain e₃ : Spec.Aes.bytesAt s₁.mem ((hSt s₀ + BitVec.ofNat 32 288).setWidth 64) (hH s₀) =
        Spec.Aes.bytesAt s₀.mem ((hSt s₀).setWidth 64 + 288) (held msg.length) := by
      rw [add_setWidth (by omega_arith), ← hn]; exact fSt' (by have := held_le (countX86 s₀).toNat; omega_arith)
    obtain ⟨hm, hne, hst, happ⟩ := Proof.Cmac.Stream.repr_finish hr
    obtain out := h₂.out (by rw [hciph, e₁]; exact hsk) _ hm (by rw [hH, hn]; exact hne)
      (by rw [hciph, e₂]; exact hst)
    rw [out, hciph, e₃, happ, Proof.Cmac.Stream.aesCmac_eq]

/-! ## Constant time -/

/-- What the call leaves. -/
structure HAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = hE s₀
  wr : s.wr = s₀.wr
  frame : Frame (HBig s₀) s₀.mem s.mem

theorem fin_after {s₀ s : State} (hp : HPre s₀) (h : HMid s₀ s) :
    WP isa (call6 ("vg_cmac_aes_finalize" ++ v.suffix) (Impl.CmacAes.X86.finalize v.callee)) s (HAft s₀) :=
  WP.mono ((fin_call v) h.args) fun s' h' => by
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
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finish v.callee v.suffix) fun _ _ => True := by
  obtain hp := HPre.of h0
  obtain hp' := HPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  obtain e0 : hSt s₀ = hSt s₀' := qa 0 (by decide)
  obtain e1 : hR s₀ = hR s₀' := by rw [hR, hR, qa 1 (by decide)]
  obtain eH : hH s₀ = hH s₀' := by rw [hH, hH, countX86, countX86, qa 2 (by decide), qa 3 (by decide)]
  obtain e4 : hO s₀ = hO s₀' := qa 4 (by decide)
  obtain e5 : hSc s₀ = hSc s₀' := qa 5 (by decide)
  obtain ag : ∀ {a b : State}, Pt 6 s₀ a → Pt 6 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 6)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  obtain a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 6))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := finPre) (by taint_decide)).wp (F₁ := HMid s₀) (F₂ := HMid s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  obtain c := ((fin_rel v (E := hE s₀) (Q := fun a b => HMid s₀ a ∧ HMid s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, eH, e4, e5]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := HAft s₀) (F₂ := HAft s₀') fun _ _ h => ⟨(fin_after v) hp h.1, (fin_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain b := RelCT.taint (A := taint) (P := fun a b => HAft s₀ a ∧ HAft s₀' b) (argTaint [] (4 + 4 * 6))
    (fun _ _ h => ag ⟨h.1.esp, h.1.wr, fun _ hi => hp.keep h.1.frame hi⟩
      ⟨h.2.esp, h.2.wr, fun _ hi => hp'.keep h.2.frame hi⟩) (c := .block (restore 5)) (by taint_decide)
  exact a.seq (c.seq b)

theorem finish_ct : ConstantTime isa finishX86.pre finishX86.pub (finish v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((finish_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86

end

end

/-! ### `CmacAes.Stream.X86.AbsorbCorrect`, which only this module used -/

section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` is correct

After `absorbPre`, the first call chains the block held back if data is left
(`b1`), the second the whole blocks of the data left but its last 1 to 16
bytes (`nb`), and the last copy holds those back. If no data is left (`len ≤
16 - h`), the calls chain nothing and the copy copies nothing, and the data is
appended to the bytes held back (`repr_fill`); otherwise `repr_chain`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

open VG.WriteBytes

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Proof.Cmac.Stream (held held_le)

theorem frame_at {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hp : p.toNat + n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd r hr _ (Offset.contains_base p (by omega_using [hi]) (by omega_using [hp, hi])) hc

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 16 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 16 1 = [Spec.Aes.bytesAt m p 16] := by
  simp [Spec.Cmac.blocksAt, k0]
where k0 : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

theorem bytesAt_zero (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 0 = [] := rfl

theorem absorb_wp {s₀ : State} (h0 : absorbX86.pre s₀) :
    WP isa (absorb v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ absorbX86.post s₀ s' := by
  obtain hp := APre.of h0
  have hL := hp.lt
  have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  have fS : (aSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have e60 := hp.esp60
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  obtain hsum := nb_le (aC s₀) (aL s₀)
  obtain hrr := rest_le (aC s₀) (aL s₀)
  obtain hh := held_le (aC s₀)
  unfold absorb
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono ((upd_call v) h₅.args) fun s₆ h₆ => ?_)
  obtain a₆ := upd_aft hp (h₅.mem ▸ m4_big hp) h₅.ctx h₅.ebp h₆
  refine WP.seq (WP.mono (chain2_mid hp a₆) fun s₇ ⟨h₇, m₇⟩ => ?_)
  refine WP.seq (WP.mono ((upd_call v) h₇.args) fun s₈ h₈ => ?_)
  obtain a₈ := upd_aft hp h₇.aft.frame h₇.aft.ctx h₇.aft.ebp h₈
  unfold absorbPost
  refine WP.seq (WP.mono (rest_wp hp a₈.ctx a₈.ebp) fun s₉ h₉ => ?_)
  -- The last copy.
  obtain hsrc : 0 < restOf (aC s₀) (aL s₀) →
      (aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀))).setWidth 64 =
        (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) :=
    fun _ => add_setWidth (by omega_arith)
  obtain p288 : (aSt s₀ + BitVec.ofNat 32 288).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
    add_setWidth (by omega_using [fSt])
  refine WP.seq (WP.mono (copy_wp (L := restOf (aC s₀) (aL s₀)) (by omega_using [hrr]) h₉.esi h₉.edi h₉.ecx
    (fun _ => by rw [add_toNat (by omega_arith)]; omega_using [fD, hsum]) (fun _ => by rw [add_toNat (by omega_using [fSt])]; omega_using [fSt, hrr])
    (fun h => by
      rw [h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨adR s₀, by simp, _, hsrc h, by simp; omega_using [hsum]⟩)
    (fun _ => by
      rw [h₉.ctx.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨astR s₀, by simp, 288, p288, by simp; omega_using [hrr]⟩)
    (fun h => by
      rw [hsrc h, p288]
      exact (hp.st_d.sub_left (Offset.sub_base (d := 288) (n := restOf (aC s₀) (aL s₀)) _ (by omega_using [hrr]))).symm.sub_left
        (Offset.sub_base (d := fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) (n := restOf (aC s₀) (aL s₀)) _
          (by omega_using [hsum])))) fun s₁₀ h₁₀ => ?_)
  obtain ⟨m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := h₁₀
  -- The frames.
  obtain f6 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩,
      below (aE s₀) 60] s₅.mem s₆.mem := by
    have := h₆.frame; rw [h₅.ctx.esp, add_setWidth (by omega_using [fSt])] at this; exact this
  obtain f8 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩,
      below (aE s₀) 60] s₆.mem s₈.mem := by
    have := h₈.frame; rw [h₇.aft.ctx.esp, add_setWidth (by omega_using [fSt]), m₇] at this; exact this
  obtain m₁₀' : s₁₀.mem = writeBytes s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
      (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)))
        (restOf (aC s₀) (aL s₀))) := by
    rw [m₁₀, h₉.mem, p288]
    by_cases hr0 : restOf (aC s₀) (aL s₀) = 0
    · rw [hr0, bytesAt_zero, bytesAt_zero]
    · rw [hsrc (by omega_using [hr0])]
  obtain hlr : (Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
      16 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))).length = restOf (aC s₀) (aL s₀) :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain fC2 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, restOf (aC s₀) (aL s₀)⟩] s₈.mem s₁₀.mem := by
    rw [m₁₀']; exact writeBytes_frame _ _ _ (by rw [hlr]; exact Region.contains_self _ _)
  obtain fSv : Frame [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩] s₀.mem (savedMem s₀ (aSc s₀)) :=
    savedMem_frame _ _
  obtain fC1 : Frame [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩]
      (savedMem s₀ (aSc s₀)) s₅.mem := by rw [h₅.mem]; exact m4_frame s₀
  let K : List Region := [⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 2176, 16⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 (288 + held (aC s₀)), fOf (aC s₀) (aL s₀)⟩,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩, below (aE s₀) 60,
    ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, restOf (aC s₀) (aL s₀)⟩]
  obtain F5 : Frame K s₀.mem s₅.mem := (fSv.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  obtain KB : Frame (ABig s₀) s₀.mem s₁₀.mem := F10.sub fun r hr => by
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨ascR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega_using [hfh])⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨ascR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨astR s₀, by simp, Offset.sub_base _ (by omega_using [hrr])⟩
  -- The saved registers.
  obtain slots : ∀ r d, (r, d) ∈ saved →
      s₁₀.mem.readW ((aSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    obtain hb := saved_bound _ hrd
    obtain Fp : Frame K.tail (savedMem s₀ (aSc s₀)) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    obtain sub : Region.Sub ⟨(aSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (ascR s₀) := Offset.sub_base _ (by omega_using [hb])
    rw [Fp.readW (Region.contains_self _ _) (fun q hq => ?_) (by decide)]
    · exact saveMem_slot _ _ _ hrd
    simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hfh]))).symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega_using [hb]) (by omega_using [hb])
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hrr]))).symm.sub_left sub
  obtain esp₁₀ : s₁₀.gpr .esp = aE s₀ := by
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), h₉.ctx.esp]
  refine WP.mono (restore_wp (s₀ := s₀) (i := 6) (Sc := aSc s₀) esp₁₀
    (by rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr]; exact hp.arg_in (by decide)) (hp.keep KB (by decide)) fS (by
      rw [rd₁₀, wr₁₀, h₉.ctx.rd, h₉.ctx.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩) slots)
    fun s₁₁ ⟨hcs, m₁₁⟩ => ?_
  obtain F11 : Frame K s₀.mem s₁₁.mem := m₁₁ ▸ F10
  -- The key, the data and the return address are in none of these.
  obtain dK : ∀ r ∈ K, (⟨(aSt s₀).setWidth 64, 272⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Offset.sub_base _ (by decide))
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hfh])
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [])
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hrr])
  obtain dDat : ∀ r ∈ K, (adR s₀).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.d_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega_using [hfh]))
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
    · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_d.symm
    · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by omega_using [hrr]))
  obtain dRet : ∀ r ∈ K, (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_s.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega_using [hfh]))
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by decide))
    · exact hp.ret_s.sub_right (Region.sub_prefix (by decide))
    · exact ret_below e60
    · exact hp.ret_st.sub_right (Offset.sub_base _ (by omega_using [hrr]))
  refine ⟨⟨hcs, F11.readW (r := ⟨(aE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) dRet (by decide)⟩, ?_⟩
  intro key msg hr hRk hcnt hlen
  show Spec.Cmac.Repr s₁₁.mem ((aSt s₀).setWidth 64) key
    (msg ++ Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀))
  obtain hcm : aC s₀ = msg.length := by
    show (countX86 s₀).toNat = _
    rw [hcnt, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hlen])
  have hR : aR s₀ = Spec.Aes.rounds (key.length / 4) := hRk
  obtain hRb : 16 * (aR s₀ + 1) ≤ 272 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain hsch := ((Proof.Cmac.Stream.repr_iff _ _ _ _).mp hr).1.2.1
  rw [← hR] at hsch
  obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
      Spec.Cmac.aesWith (aR s₀) (Spec.Aes.bytesAt m ((aSt s₀).setWidth 64) (16 * (aR s₀ + 1))) =
        Spec.Cmac.aes key := fun m hf => by
    rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb]), hsch,
      Spec.Cmac.aes, ← hR]
  -- The data, wherever it is read.
  obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ aL s₀ →
      Spec.Aes.bytesAt m ((aD s₀).setWidth 64 + BitVec.ofNat 64 a) b =
        ((Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).drop a).take b := fun m hf a b hab => by
    rw [Proof.Cmac.Stream.bytesAt_offset m _ hab, Proof.Cmac.bytesAt_frame hf dDat (by omega_using [fD])]
  obtain fS' : Frame K s₀.mem (savedMem s₀ (aSc s₀)) := fSv.mono (by simp [K])
  -- The chaining value.
  obtain cv5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 := by
    rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [hfh]))
        (by decide),
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
  obtain cv11 : Spec.Aes.bytesAt s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 =
      Spec.Aes.bytesAt s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) 16 := by
    rw [m₁₁]
    exact Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_using []) (by omega_using []) (by omega_using [hrr]))
      (by decide)
  have out6 := h₆.out
  rw [add_setWidth (by omega_using [fSt]), add_setWidth (by omega_using [fSt]), ciph _ F5] at out6
  have out8 := h₈.out
  rw [add_setWidth (by omega_using [fSt]), m₇, ciph _ F6] at out8
  obtain hk : ∀ i < 272, s₁₁.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) =
      s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 i) :=
    fun i hi => frame_at F11 dK (by simp only [BitVec.toNat_setWidth]; omega_using []) hi
  obtain hdl : (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).length = aL s₀ :=
    Proof.Cmac.bytesAt_length _ _ _
  obtain hlf : (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))).length =
      fOf (aC s₀) (aL s₀) := Proof.Cmac.bytesAt_length _ _ _
  -- The bytes held back so far, and the first `f` bytes of data after them.
  obtain hb5 : Spec.Aes.bytesAt s₅.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
      (held (aC s₀) + fOf (aC s₀) (aL s₀)) =
      Spec.Aes.bytesAt s₀.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) (held (aC s₀)) ++
        (Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀)).take (fOf (aC s₀) (aL s₀)) := by
    obtain e := bytesAt_writeBytes (savedMem s₀ (aSc s₀)) ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) (held (aC s₀))
      (Spec.Aes.bytesAt (savedMem s₀ (aSc s₀)) ((aD s₀).setWidth 64) (fOf (aC s₀) (aL s₀))) (by rw [hlf]; omega_using [hfh])
    rw [hlf] at e
    rw [h₅.mem, m4, ← Offset.add_add, e,
      Proof.Cmac.bytesAt_frame fSv (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hh]))).sub_right (Offset.sub_base _ (by decide)))
        (by omega_using [hh])]
    refine congrArg (_ ++ ·) ?_
    have := dat _ fS' 0 (fOf (aC s₀) (aL s₀)) (by omega_using [hsum])
    rwa [BitVec.add_zero, List.drop_zero] at this
  generalize hd : Spec.Aes.bytesAt s₀.mem ((aD s₀).setWidth 64) (aL s₀) = d at hdl hb5 dat ⊢
  by_cases hx : leftOf (aC s₀) (aL s₀) = 0
  · -- Everything fits in the block held back.
    obtain hfL' : fOf (aC s₀) (aL s₀) = aL s₀ := by unfold leftOf at hx; omega_using [hsum, hx]
    obtain hb : b1Of (aC s₀) (aL s₀) = 0 := by simp [b1Of, hx]
    obtain hn : nbOf (aC s₀) (aL s₀) = 0 := by simp [nbOf, hx]
    obtain hr0 : restOf (aC s₀) (aL s₀) = 0 := rest_zero hx
    obtain m118 : s₁₁.mem = s₈.mem := by
      rw [m₁₁, m₁₀', hr0, bytesAt_zero, writeBytes_nil]
    refine Proof.Cmac.Stream.repr_fill hr hk (by rw [hdl, ← hcm]; omega_using [hfh, hfL']) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _
      rw [cv11, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
      exact cv5
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ =
        Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ ++ _
      rw [← hcm, hdl]
      obtain sub : Region.Sub ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, held (aC s₀) + aL s₀⟩ (astR s₀) :=
        Offset.sub_base _ (by omega_using [hfh, hfL'])
      obtain dj : ∀ r ∈ [⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩, ⟨(aSc s₀).setWidth 64, 2176⟩,
          below (aE s₀) 60], (⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 288, held (aC s₀) + aL s₀⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
        · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right sub).symm
      have hb5' := hb5
      rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
      rw [m118, Proof.Cmac.bytesAt_frame f8 dj (by omega_using [hfh, hfL']), Proof.Cmac.bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
  · -- The block held back is complete, and more blocks may follow.
    obtain hlt : 16 - held (aC s₀) < aL s₀ := by unfold leftOf fOf at hx; omega_using [hx]
    obtain hf' : fOf (aC s₀) (aL s₀) = 16 - held (aC s₀) := by unfold fOf; omega_using [hlt]
    obtain hb : b1Of (aC s₀) (aL s₀) = 1 := by simp [b1Of, hx]
    obtain hn : nbOf (aC s₀) (aL s₀) = Proof.Cmac.Stream.nblocks (aC s₀) (aL s₀) := by
      simp only [nbOf, hx, ↓reduceIte]
      unfold leftOf Proof.Cmac.Stream.nblocks
      rw [hf']
    obtain hd2 : (d2Of s₀).setWidth 64 = (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)) := by
      simp only [d2Of, hx, ↓reduceIte]; exact add_setWidth (by omega_using [fD, hlt, hf'])
    have hb5' := hb5
    rw [hf', Nat.add_sub_cancel' hh] at hb5'
    refine Proof.Cmac.Stream.repr_chain hr hk (by rw [hdl, ← hcm]; exact hlt) ?_ ?_
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _ =
        Spec.Cmac.chain _ (Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 272) _)
          ([Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ ++ _] ++ _)
      rw [← hcm, hdl]
      rw [cv11, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, hd2, Proof.Cmac.Stream.blocksAt_eq,
        dat _ F6 _ _ (by omega_using [hsum]), hb5', hf', hn]
    · show Spec.Aes.bytesAt _ ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288) _ = _
      rw [← hcm, hdl]
      obtain e := bytesAt_writeBytes_self s₈.mem ((aSt s₀).setWidth 64 + BitVec.ofNat 64 288)
        (xs := Spec.Aes.bytesAt s₈.mem ((aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀) +
          16 * nbOf (aC s₀) (aL s₀))) (restOf (aC s₀) (aL s₀))) (by rw [hlr]; omega_using [hrr])
      rw [hlr] at e
      obtain hr' : aL s₀ - (16 - held (aC s₀)) - 16 * Proof.Cmac.Stream.nblocks (aC s₀) (aL s₀) =
          restOf (aC s₀) (aL s₀) := by
        rw [← hn, ← hf']; rfl
      rw [hr', m₁₁, m₁₀', e, dat _ F8 _ _ (by omega_using [hsum]),
        List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
        List.drop_drop, ← hn, hf']

end VG.Proof.CmacAes.Stream.X86

end

end

/-! ### `CmacAes.Stream.X86.Init`, which only this module used -/

section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_init`

The code saves the registers in the scratch buffer, expands the key into the
state, derives the subkeys after the schedule, zeroes the chaining value and
restores the registers: the state then represents the empty message. The code
between the calls is constant time by the taint analysis (from `esp` and the
stack arguments), and the calls by their own proofs (`ek_rel`, `sub_rel`),
their arguments pinned by `IMid₁` and `IMid₂`.
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_addi wp_shr)
open VG.Proof.CmacAes.X86 (wp_arg zero4_ok)

section
variable (s₀ : State)

abbrev iSt : BitVec 32 := arg s₀ 0
abbrev iKp : BitVec 32 := arg s₀ 1
abbrev iKL : Nat := (arg s₀ 2).toNat
abbrev iSc : BitVec 32 := arg s₀ 3
abbrev iE : BitVec 32 := s₀.gpr .esp
abbrev istR : Region := ⟨(iSt s₀).setWidth 64, 304⟩
abbrev ikR : Region := ⟨(iKp s₀).setWidth 64, iKL s₀⟩
abbrev iscR : Region := ⟨(iSc s₀).setWidth 64, 2304⟩
abbrev iaR : Region := ⟨argAddr s₀ 0, 16⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev IBig : List Region := [istR s₀, iscR s₀, below (iE s₀) 52]

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [ikR s₀, iaR s₀]
  wr : s₀.wr = [istR s₀, iscR s₀]
  st_k : (istR s₀).Disjoint (ikR s₀)
  st_s : (istR s₀).Disjoint (iscR s₀)
  k_s : (ikR s₀).Disjoint (iscR s₀)
  a_st : (iaR s₀).Disjoint (istR s₀)
  a_s : (iaR s₀).Disjoint (iscR s₀)
  ret_st : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (istR s₀)
  ret_s : (⟨(iE s₀).setWidth 64, 4⟩ : Region).Disjoint (iscR s₀)
  b_st' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 52, 52⟩ : Region).Disjoint (istR s₀)
  b_k' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 52, 52⟩ : Region).Disjoint (ikR s₀)
  b_s' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 52, 52⟩ : Region).Disjoint (iscR s₀)
  fSt : (iSt s₀).toNat + 304 ≤ 2 ^ 32
  fK : (iKp s₀).toNat + iKL s₀ ≤ 2 ^ 32
  fS : (iSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp52 : 52 ≤ (iE s₀).toNat
  espfit : (iE s₀).toNat + 20 ≤ 2 ^ 32
  klen : iKL s₀ = 16 ∨ iKL s₀ = 24 ∨ iKL s₀ = 32

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

namespace IPre
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem b_st : (below (iE s₀) 52).Disjoint (istR s₀) := by rw [below_eq hp.esp52]; exact hp.b_st'
theorem b_k : (below (iE s₀) 52).Disjoint (ikR s₀) := by rw [below_eq hp.esp52]; exact hp.b_k'
theorem b_s : (below (iE s₀) 52).Disjoint (iscR s₀) := by rw [below_eq hp.esp52]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.espfit; omega_arith

theorem arg_in {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨iaR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `IBig` changes. -/
theorem keep {m : Mem} (hf : Frame (IBig s₀) s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp52).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 4 s₀ := by
  refine ⟨by have := hp.espfit; omega_arith, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega_arith) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega_arith) hp.ret_s hp.a_s

end IPre

theorem IPre.savedMem_big {s₀ : State} (_hp : IPre s₀) : Frame (IBig s₀) s₀.mem (savedMem s₀ (iSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨iscR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before the first call -/

theorem initPre_eq : initPre = .mov .eax (argOp 3) :: (save ++ ([.mov .eax (argOp 1), .mov .ecx (argOp 2),
    .mov .edx (argOp 0), .mov .ebx (argOp 3)] : List Instr)) := rfl

/-- What the code before the first call leaves. -/
structure IMid₁ (s₀ s : State) : Prop where
  args : EArgs s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀)
  esp : s.gpr .esp = iE s₀
  mem : s.mem = savedMem s₀ (iSc s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa (.block initPre) s₀ (IMid₁ s₀) := by
  have fS := hp.fS
  have fSt := hp.fSt
  have e52 := hp.esp52
  rw [initPre_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine save_wp (Sc := iSc s₀) u₁.gpr fS (by
      rw [u₁.wr, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩)
    fun s₂ g₂ rd₂ wr₂ m₂ => ?_
  obtain hm₂ : s₂.mem = savedMem s₀ (iSc s₀) := by
    rw [m₂, u₁.mem, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  obtain esp₂ : s₂.gpr .esp = iE s₀ := by rw [g₂, u₁.other _ (by decide)]
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr]
  obtain av : ∀ i < 4, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.savedMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂', wr₂']; exact hp.arg_in (by decide)) (av 1 (by decide))
    fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide)) (by rw [u₃.mem]; exact av 2 (by decide))
    fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 0 (by decide)) fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂', wr₂']; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₆ u₆ => WP.block_nil ?_
  obtain esp₆ : s₆.gpr .esp = iE s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂']
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂']
  obtain b20 : Region.Sub (below (iE s₀) 20) (below (iE s₀) 52) := below_sub (by decide) e52
  refine ⟨?_, esp₆, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂], rd₆, wr₆⟩
  exact
  { eax := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    ecx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; exact arg_ofNat s₀ 2
    edx := by rw [u₆.other _ (by decide), u₅.gpr]
    ebx := u₆.gpr
    klen := hp.klen
    esp := by rw [esp₆]; omega_arith
    kw := hp.st_k.symm.sub_right (Region.sub_prefix (by decide))
    ks := hp.k_s.sub_right (Region.sub_prefix (by decide))
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₆]; exact hp.b_k.sub_left b20
    bW := by rw [esp₆]; exact (hp.b_st.sub_left b20).sub_right (Region.sub_prefix (by decide))
    bS := by rw [esp₆]; exact (hp.b_s.sub_left b20).sub_right (Region.sub_prefix (by decide))
    fK := hp.fK
    fW := by omega_arith
    fS := by omega_arith
    reads := by
      rw [rd₆, wr₆, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ikR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₆, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨istR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## After a call -/

/-- What is known after each call. -/
structure IAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = iE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (IBig s₀) s₀.mem s.mem

theorem IAft.pt {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) : Pt 4 s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.keep h.frame hi⟩

theorem IMid₁.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₁ s₀ s)
    (h' : EPost s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.esp, h.mem] at fr
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    hp.savedMem_big.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨istR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (iE s₀) 52, by simp, below_sub (by decide) hp.esp52⟩

theorem ek_after {s₀ s : State} (hp : IPre s₀) (h : IMid₁ s₀ s) :
    WP isa (call4 v.expand.name v.expand.code) s (IAft s₀) :=
  WP.mono ((ek_call v) h.args) fun _ h' => h.after hp h'

/-! ## Between the calls -/

theorem rounds32 {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 32 KL >>> 2 + 6 = BitVec.ofNat 32 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-- What the code between the calls leaves. -/
structure IMid₂ (s₀ s : State) : Prop where
  args : SArgs s (iSt s₀) (iSt s₀ + BitVec.ofNat 32 240) (iSc s₀) (iKL s₀ / 4 + 6)
  aft : IAft s₀ s

theorem initMid_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) :
    WP isa (.block initMid) s fun s' => IMid₂ s₀ s' ∧ s'.mem = s.mem := by
  have fS := hp.fS
  have fSt := hp.fSt
  have e52 := hp.esp52
  obtain rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain av : ∀ i < 4, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.keep h.frame hi
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (av 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact av 2 (by decide))
    fun s₂ u₂ => ?_
  refine wp_shr (by decide) fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_mov fun s₅ u₅ => wp_addi fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, rw₀]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact av 3 (by decide)) fun s₇ u₇ => WP.block_nil ?_
  obtain esp₇ : s₇.gpr .esp = iE s₀ := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  obtain kSt : Region.Sub ⟨(iSt s₀ + BitVec.ofNat 32 240).setWidth 64, 32⟩ (istR s₀) := by
    rw [add_setWidth (by omega_arith)]; exact Offset.sub_base _ (by decide)
  obtain hR : iKL s₀ / 4 + 6 = 10 ∨ iKL s₀ / 4 + 6 = 12 ∨ iKL s₀ / 4 + 6 = 14 := by
    rcases hp.klen with h | h | h <;> rw [h] <;> decide
  refine ⟨⟨?_, ⟨esp₇, rd₇, wr₇, by rw [m₇]; exact h.frame⟩⟩, m₇⟩
  exact
  { eax := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    ecx := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
        arg_ofNat s₀ 2]
      exact rounds32 hp.klen
    edx := by
      rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr]; rfl
    ebx := u₇.gpr
    rounds := hR
    esp := by rw [esp₇]; exact e52
    wk := by
      rw [add_setWidth (by omega_arith)]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    ks := (hp.st_s.sub_left kSt).sub_right (Region.sub_prefix (by decide))
    bW := by rw [esp₇]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bK := by rw [esp₇]; exact hp.b_st.sub_right kSt
    bS := by rw [esp₇]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega_arith
    fK := by rw [add_toNat (by omega_arith)]; omega_arith
    fS := by omega_arith
    reads := by
      rw [rd₇, wr₇, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₇, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨istR s₀, by simp, 240, add_setWidth (by omega_arith), by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

theorem IMid₂.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₂ s₀ s)
    (h' : SPost s (iSt s₀) (iSt s₀ + BitVec.ofNat 32 240) (iSc s₀) (iKL s₀ / 4 + 6) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.aft.esp] at fr
  have fSt := hp.fSt
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.aft.esp], by rw [h'.rd, h.aft.rd],
    by rw [h'.wr, h.aft.wr], h.aft.frame.trans (fr.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨istR s₀, by simp, ?_⟩
    rw [add_setWidth (by omega_arith)]; exact Offset.sub_base _ (by decide)
  · exact ⟨iscR s₀, by simp, Region.sub_prefix (by decide)⟩
  · exact ⟨below (iE s₀) 52, by simp, fun _ h => h⟩

theorem sub_after {s₀ s : State} (hp : IPre s₀) (h : IMid₂ s₀ s) :
    WP isa (call4 ("vg_cmac_aes_subkeys" ++ v.suffix) (Impl.CmacAes.X86.subkeys v.callee)) s (IAft s₀) :=
  WP.mono ((sub_call v) h.args) fun _ h' => h.after hp h'

/-! ## After the calls -/

theorem initPost_eq : initPost = .mov .edx (argOp 0) :: (Impl.CmacAes.X86.zero4 .edx 272 ++ restore 3) := rfl

/-- The chaining value zeroed, and the registers restored from their slots. -/
theorem initPost_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s)
    (hs : ∀ r d, (r, d) ∈ saved → s.mem.readW ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r) :
    WP isa (.block initPost) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.mem = Proof.Cmac.zero4 s.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 272) := by
  have fS : (arg s₀ 3).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  obtain rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  rw [initPost_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (hp.keep h.frame (by decide))
    fun s₁ u₁ => ?_
  refine zero4_ok (by decide) (by rw [u₁.gpr]; omega_arith) (by
      rw [u₁.wr, h.wr, hp.wr, u₁.gpr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, 272, rfl, by simp⟩)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  obtain hz : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩] s.mem s₂.mem := by
    rw [m₂, u₁.mem, u₁.gpr]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine WP.mono (restore_wp (s₀ := s₀) (i := 3) (Sc := iSc s₀) (by rw [g₂ _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [rd₂, wr₂, u₁.rd, u₁.wr, rw₀]; exact hp.arg_in (by decide))
    (by
      rw [hz.readW (r := ⟨argAddr s₀ 3, 4⟩) (Region.contains_self _ _) (fun q hq => by
          simp only [List.mem_singleton] at hq; subst hq
          exact (hp.a_st.sub_left (arg_sub hp.fit (by decide))).sub_right (Offset.sub_base _ (by decide)))
        (by decide)]
      exact hp.keep h.frame (by decide))
    fS (by
      rw [rd₂, wr₂, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩)
    fun r d hrd => ?_) fun s' ⟨hcs, hm⟩ => ⟨hcs, by rw [hm, m₂, u₁.mem, u₁.gpr]⟩
  obtain hb := saved_bound _ hrd
  rw [hz.readW (r := ⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (Offset.sub_base _ (by omega_arith)))
    (by decide)]
  exact hs r d hrd

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa (init v.expand v.callee v.suffix) s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  obtain hp := IPre.of h0
  have fS : (arg s₀ 3).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have fSt : (arg s₀ 0).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fSt' : (iSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have e52 := hp.esp52
  unfold init
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono ((ek_call v) h₁.args) fun s₂ h₂ => ?_)
  obtain a₂ := h₁.after hp h₂
  refine WP.seq (WP.mono (initMid_wp hp a₂) fun s₃ ⟨h₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono ((sub_call v) h₃.args) fun s₄ h₄ => ?_)
  obtain a₄ := h₃.after hp h₄
  obtain f₂ : Frame [⟨(iSt s₀).setWidth 64, 240⟩, ⟨(iSc s₀).setWidth 64, 512⟩, below (iE s₀) 52] s₁.mem s₂.mem := by
    have := h₂.frame
    rw [h₁.esp] at this
    refine this.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨below (iE s₀) 52, by simp, below_sub (by decide) e52⟩
  obtain f₄ : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(iSc s₀).setWidth 64, 2176⟩,
      below (iE s₀) 52] s₂.mem s₄.mem := by
    have := h₄.frame; rw [h₃.aft.esp, m₃, add_setWidth (by omega_arith)] at this; exact this
  -- The saved registers.
  obtain dSlot : ∀ d, 2176 ≤ d → d + 4 ≤ 2192 → ∀ r ∈ [⟨(iSt s₀).setWidth 64, 240⟩, ⟨(iSc s₀).setWidth 64, 512⟩,
      below (iE s₀) 52, ⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 240, 32⟩, ⟨(iSc s₀).setWidth 64, 2176⟩],
      (⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := fun d h₁ h₂ r hr => by
    obtain sub : Region.Sub ⟨(iSc s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩ (iscR s₀) := Offset.sub_base _ (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact hp.b_s.symm.sub_left sub
    · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  obtain slots : ∀ r d, (r, d) ∈ saved →
      s₄.mem.readW ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := fun r d hrd => by
    obtain hb := saved_bound _ hrd
    obtain c := Region.contains_self ((iSc s₀).setWidth 64 + BitVec.ofNat 64 d) 4
    rw [f₄.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide),
      f₂.readW c (fun q hq => dSlot d hb.1 hb.2 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq ⊢; rcases hq with h | h | h <;> simp [h]))
        (by decide), h₁.mem]
    exact saveMem_slot _ _ _ hrd
  refine WP.mono (initPost_wp hp a₄ slots) fun s₅ ⟨hcs, m₅⟩ => ?_
  obtain fz : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩] s₄.mem s₅.mem := by
    rw [m₅]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain F₅ : Frame (IBig s₀) s₀.mem s₅.mem := a₄.frame.trans (fz.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  refine ⟨⟨hcs, F₅.readW (r := ⟨(iE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_s
    · exact ret_below e52
  · show Spec.Cmac.Repr s₅.mem ((iSt s₀).setWidth 64) (Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)) []
    rw [Proof.Cmac.Stream.repr_iff]
    obtain hlen : (Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)).length = iKL s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    obtain hkey : Spec.Aes.bytesAt s₁.mem ((iKp s₀).setWidth 64) (iKL s₀) =
        Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀) := by
      rw [h₁.mem]
      exact Proof.Cmac.bytesAt_frame (savedMem_frame _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.k_s.sub_right (Offset.sub_base _ (by decide))) (by have := hp.fK; omega_arith)
    obtain dz : ∀ {d n : Nat}, d + n ≤ 272 →
        ∀ r ∈ [(⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩ : Region)],
          (⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := fun {d n} hd r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    -- The schedule, from the first call on.
    obtain sch : ∀ {d n : Nat}, d + n ≤ 240 →
        Spec.Aes.bytesAt s₅.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 d) n =
          Spec.Aes.bytesAt s₂.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 d) n := fun {d n} hd => by
      rw [Proof.Cmac.bytesAt_frame fz (dz (by omega_arith)) (by omega_arith), Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
        · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by decide))
        · exact (hp.b_st.sub_right (Offset.sub_base _ (by omega_arith))).symm) (by omega_arith)]
    obtain hRb : 16 * (Spec.Aes.rounds (iKL s₀ / 4) + 1) ≤ 240 := by
      have := hp.klen; simp only [Spec.Aes.rounds]; omega_arith
    obtain hsch : Spec.Aes.bytesAt s₂.mem ((iSt s₀).setWidth 64) (16 * (Spec.Aes.rounds (iKL s₀ / 4) + 1)) =
        Spec.Aes.expandKey (Spec.Aes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)) := by rw [h₂.out, hkey]
    obtain k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by simp [Proof.Cmac.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [hlen]
      have := sch (d := 0) (n := 16 * (Spec.Aes.rounds (iKL s₀ / 4) + 1)) (by omega_arith)
      rw [k0] at this; rw [this, hsch]
    · have e : Spec.Aes.bytesAt s₅.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
          Spec.Aes.bytesAt s₄.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 240) 32 :=
        Proof.Cmac.bytesAt_frame fz (dz (d := 240) (n := 32) (by omega_arith)) (by decide)
      rw [show (iSt s₀).setWidth 64 + 240 = (iSt s₀).setWidth 64 + BitVec.ofNat 64 240 from rfl, e]
      have o := h₄.out
      rw [add_setWidth (by omega_arith), m₃, show iKL s₀ / 4 + 6 = Spec.Aes.rounds (iKL s₀ / 4) from rfl, hsch] at o
      rw [o]
      simp only [Spec.Cmac.aes, hlen]
    · rw [m₅]; exact (Proof.Cmac.zero4_bytes _ _).trans rfl

/-! ## Constant time -/

theorem init_rel {s₀ s₀' : State} (h0 : initX86.pre s₀) (h0' : initX86.pre s₀') (hq : initX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (init v.expand v.callee v.suffix) fun _ _ => True := by
  obtain hp := IPre.of h0
  obtain hp' := IPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  obtain e0 : iSt s₀ = iSt s₀' := qa 0 (by decide)
  obtain e1 : iKp s₀ = iKp s₀' := qa 1 (by decide)
  obtain e2 : iKL s₀ = iKL s₀' := by rw [iKL, iKL, qa 2 (by decide)]
  obtain e3 : iSc s₀ = iSc s₀' := qa 3 (by decide)
  obtain ag : ∀ {a b : State}, Pt 4 s₀ a → Pt 4 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 4)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  obtain a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := .block initPre) (by taint_decide)).wp (F₁ := IMid₁ s₀) (F₂ := IMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  obtain e := ((ek_rel v (E := iE s₀) (P := fun a b => IMid₁ s₀ a ∧ IMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨(ek_after v) hp h.1, (ek_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain m := ((RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initMid) (by taint_decide)).wp
    (F₁ := fun s => IMid₂ s₀ s) (F₂ := fun s => IMid₂ s₀' s)
    fun _ _ h => ⟨WP.mono (initMid_wp hp h.1) fun _ h => h.1, WP.mono (initMid_wp hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  obtain sk := ((sub_rel v (E := iE s₀) (P := fun a b => IMid₂ s₀ a ∧ IMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e2, e3]; exact h.2.args, h.1.aft.esp, by rw [h.2.aft.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨(sub_after v) hp h.1, (sub_after v) hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  obtain p := RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initPost) (by taint_decide)
  exact a.seq (e.seq (m.seq (sk.seq p)))

theorem init_ct : ConstantTime isa initX86.pre initX86.pub (init v.expand v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((init_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86

end

end

@[expose] public section

section

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
`esp`, the stack arguments and `ebp`, which the correctness proof pins to a
value of the public arguments (`AAft`), and each call of `vg_cmac_aes_update`,
in its frame, is constant time by its own proof (`upd_rel`), its arguments
pinned by `AMid₁` and `AMid₂`.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbX86.pre s₀) (h0' : absorbX86.pre s₀')
    (hq : absorbX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (absorb v.callee v.suffix) fun _ _ => True := by
  have hp := APre.of h0
  have hp' := APre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have eSt : aSt s₀ = aSt s₀' := qa 0 (by decide)
  have eR : aR s₀ = aR s₀' := by rw [aR, aR, qa 1 (by decide)]
  have eC : aC s₀ = aC s₀' := by rw [aC, aC, countX86, countX86, qa 2 (by decide), qa 3 (by decide)]
  have eD : aD s₀ = aD s₀' := qa 4 (by decide)
  have eL : aL s₀ = aL s₀' := by rw [aL, aL, qa 5 (by decide)]
  have eS : aSc s₀ = aSc s₀' := qa 6 (by decide)
  have e2 : d2Of s₀ = d2Of s₀' := by rw [d2Of, d2Of, eC, eL, eSt, eD]
  have ag : ∀ {rs : List Reg} {a b : State}, Pt 7 s₀ a → Pt 7 s₀' b → (∀ r ∈ rs, a.gpr r = b.gpr r) →
      VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) a b :=
    fun h₁ h₂ hr => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ hr
  have bp : ∀ {v v' : Nat} {a b : State}, v = v' → AAft s₀ v a → AAft s₀' v' b → ∀ r ∈ [Reg.ebp], a.gpr r = b.gpr r :=
    fun e h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ebp, h₂.ebp, e]
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 7))
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _) fun r hr => by simp at hr)
    (c := absorbPre) (by taint_decide)).wp (F₁ := AMid₁ s₀) (F₂ := AMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨absorbPre_wp hp, absorbPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have c₁ := ((upd_rel v (E := aE s₀) (P := fun a b => AMid₁ s₀ a ∧ AMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL]; exact h.2.args, h.1.ctx.esp,
        by rw [h.2.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀))) (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨(call1_after v) hp h.1, (call1_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m := ((RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2))
    (c := chain2) (by taint_decide)).wp (F₁ := AMid₂ s₀) (F₂ := AMid₂ s₀')
    fun _ _ h => ⟨WP.mono (chain2_mid hp h.1) fun _ h => h.1, WP.mono (chain2_mid hp' h.2) fun _ h => h.1⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2
  have c₂ := ((upd_rel v (E := aE s₀) (P := fun a b => AMid₂ s₀ a ∧ AMid₂ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [eSt, eS, eR, eC, eL, e2]; exact h.2.args, h.1.aft.ctx.esp,
        by rw [h.2.aft.ctx.esp]; exact qE.symm⟩).wp
      (F₁ := AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)))
      (F₂ := AAft s₀' (fOf (aC s₀') (aL s₀') + 16 * nbOf (aC s₀') (aL s₀')))
      fun _ _ h => ⟨(call2_after v) hp h.1, (call2_after v) hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => AAft s₀ (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀)) a ∧
      AAft s₀' (fOf (aC s₀') (aL s₀') + 16 * nbOf (aC s₀') (aL s₀')) b) (argTaint [.ebp] (4 + 4 * 7))
    (fun _ _ h => ag h.1.ctx.pt h.2.ctx.pt (bp (by rw [eC, eL]) h.1 h.2)) (c := absorbPost) (by taint_decide)
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbX86.pre absorbX86.pub (absorb v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => ((absorb_rel v) h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Stream.X86

end

/-!
# Streaming AES-CMAC on x86: `Verified`

Correctness and constant time, a state satisfying each precondition, and the
shared contracts of `Spec/Cmac/Contract.lean`, with 52 bytes of stack for
`init` (a call of `vg_cmac_aes_subkeys`: its four arguments, the return
address, and its call of `vg_aes_ctr32_to`) and 60 for `absorb` and `finish` (as
`init`, with six arguments).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem init_spSafe :
    (init v.expand v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [init, call4, Code.all, v.expandSpSafe, Proof.CmacAes.X86.subkeys_spSafe v]
  decide +kernel

theorem absorb_spSafe :
    (absorb v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy,
    chain1, chain2, Code.all, Proof.CmacAes.X86.update_spSafe v]
  decide +kernel

theorem finish_spSafe :
    (finish v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true := by
  simp only [finish, finPre, call6, countHeld, held, Code.all, Proof.CmacAes.X86.finalize_spSafe v]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition: the state at
`0x1000`, a key of 16 bytes at `0x3000` and the scratch buffer at `0x4000`,
as stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x800c then 16
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x3000, 16⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem init_verified : Verified X86.target (init v.expand v.callee v.suffix) (initScratchContract X86.abi 52) :=
  Verified.of_correct (fun _ hs => (init_wp v) hs) (init_ct v) (by
    have a0 : arg initSat 0 = 0x1000 := by decide
    have a1 : arg initSat 1 = 0x3000 := by decide
    have a2 : arg initSat 2 = 16 := by decide
    have a3 : arg initSat 3 = 0x4000 := by decide
    have e : argAddr initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [initScratchContract, initScratchSig, Spec.Cmac.aesInitPre, Spec.Cmac.aesInitPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, initX86] [a0, a1, a2, a3, e, esp] using initSat)

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition: the state at
`0x1000`, 10 rounds, `count` 0, no data at `0x3000` and the scratch buffer
at `0x4000`, as stack arguments at `0x8004`. -/
def absorbSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x8015 then 0x30 else if a = 0x801d then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8004, 28⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x4000, 2304⟩]

theorem absorb_verified : Verified X86.target (absorb v.callee v.suffix) (absorbScratchContract X86.abi 60) :=
  Verified.of_correct (fun _ hs => (absorb_wp v) hs) (absorb_ct v) (by
    have a0 : arg absorbSat 0 = 0x1000 := by decide
    have a1 : arg absorbSat 1 = 10 := by decide
    have a2 : arg absorbSat 2 = 0 := by decide
    have a3 : arg absorbSat 3 = 0 := by decide
    have a4 : arg absorbSat 4 = 0x3000 := by decide
    have a5 : arg absorbSat 5 = 0 := by decide
    have a6 : arg absorbSat 6 = 0x4000 := by decide
    have e : argAddr absorbSat 0 = 0x8004 := by decide
    have esp : absorbSat.gpr .esp = 0x8000 := rfl
    sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.aesAbsorbPre, Spec.Cmac.aesAbsorbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, absorbX86, countX86] [a0, a1, a2, a3, a4, a5, a6, e, esp] using absorbSat)

/-- A state satisfying `vg_cmac_aes_finish`'s precondition: the state at
`0x1000`, 10 rounds, `count` 0, `out` at `0x2000` and the scratch buffer at
`0x4000`, as stack arguments at `0x8004`. -/
def finishSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x8015 then 0x20 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x8004, 24⟩]
  wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩, ⟨0x4000, 2304⟩]

theorem finish_verified : Verified X86.target (finish v.callee v.suffix) (finishScratchContract X86.abi 60) :=
  Verified.of_correct (fun _ hs => (finish_wp v) hs) (finish_ct v) (by
    have a0 : arg finishSat 0 = 0x1000 := by decide
    have a1 : arg finishSat 1 = 10 := by decide
    have a2 : arg finishSat 2 = 0 := by decide
    have a3 : arg finishSat 3 = 0 := by decide
    have a4 : arg finishSat 4 = 0x2000 := by decide
    have a5 : arg finishSat 5 = 0x4000 := by decide
    have e : argAddr finishSat 0 = 0x8004 := by decide
    have esp : finishSat.gpr .esp = 0x8000 := rfl
    sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.aesFinishPre, Spec.Cmac.aesFinishPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, finishX86, countX86] [a0, a1, a2, a3, a4, a5, e, esp] using finishSat)

end VG.Proof.CmacAes.Stream.X86

end

end

/-!
# Streaming AES-CMAC on x86, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it and copies the
arguments passed on the stack (`Verified.stackScratch`): the return address,
the copied argument slots (three for `init`, six for `absorb`, five for
`finish`) and the 2304 bytes of working space. The copies are read only
where the pre- and postconditions read the buffers
(`Proof/CmacAes/Stream/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

theorem noEsp_of {c : Prog isa} (h : NoSp c) :
    c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by simp [h i hi]

variable (v : Proof.Aes.X86.Ctr32Impl)

theorem init_noEsp : (init v.expand v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [init, call4, Code.allInstrs, noEsp_of v.expandNosp,
    noEsp_of (Proof.CmacAes.X86.subkeys_nosp v)]
  decide +kernel

theorem absorb_noEsp : (absorb v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy, chain1, chain2,
    Code.allInstrs, noEsp_of (Proof.CmacAes.X86.update_nosp v)]
  decide +kernel

theorem finish_noEsp : (finish v.callee v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [finish, finPre, call6, countHeld, held, Code.allInstrs,
    noEsp_of (Proof.CmacAes.X86.finalize_nosp v)]
  decide +kernel

theorem init_stackUse : stackUse (init v.expand v.callee v.suffix) ≤ 52 := by
  simp only [init, call4, stackUse, v.expandStack, Proof.CmacAes.X86.subkeys_stack v]
  decide +kernel

theorem absorb_stackUse : stackUse (absorb v.callee v.suffix) ≤ 60 := by
  have h := Proof.CmacAes.X86.update_stack v
  simp only [absorb, absorbPre, absorbPost, call6, countHeld, held, fill, copy, chain1, chain2,
    stackUse]
  generalize stackUse (Impl.CmacAes.X86.update v.callee) = x at h ⊢
  revert x
  decide +kernel

theorem finish_stackUse : stackUse (finish v.callee v.suffix) ≤ 60 := by
  simp only [finish, finPre, call6, countHeld, held, stackUse, Proof.CmacAes.X86.finalize_stack v]
  decide +kernel

/-- A state satisfying `vg_cmac_aes_init`'s precondition, without the
working space: the state at `0x1000` and a key of 16 bytes at `0x3000`, as
stack arguments at `0x8004`. -/
def initFrameSat : State :=
  { initSat with rd := [⟨0x3000, 16⟩, ⟨0x8004, 12⟩], wr := [⟨0x1000, 304⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.aesInitContract X86.abi 2376).pre s := by
  implies_sat [Spec.Cmac.aesInitContract, Spec.Cmac.aesInitSig, Spec.Cmac.aesInitPre,
    Spec.Cmac.aesInitPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initFrameSat

/-- A state satisfying `vg_cmac_aes_absorb`'s precondition, without the
working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { absorbSat with rd := [⟨0x3000, 0⟩, ⟨0x8004, 24⟩], wr := [⟨0x1000, 304⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.aesAbsorbContract X86.abi 2396).pre s := by
  implies_sat [Spec.Cmac.aesAbsorbContract, Spec.Cmac.aesAbsorbSig, Spec.Cmac.aesAbsorbPre,
    Spec.Cmac.aesAbsorbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [absorbFrameSat, absorbSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using absorbFrameSat

/-- A state satisfying `vg_cmac_aes_finish`'s precondition, without the
working space: as `finishSat`. -/
def finishFrameSat : State :=
  { finishSat with rd := [⟨0x8004, 20⟩], wr := [⟨0x1000, 304⟩, ⟨0x2000, 16⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.aesFinishContract X86.abi 2392).pre s := by
  implies_sat [Spec.Cmac.aesFinishContract, Spec.Cmac.aesFinishSig, Spec.Cmac.aesFinishPre,
    Spec.Cmac.aesFinishPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finishFrameSat, finishSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finishFrameSat

theorem init_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2324 3 (init v.expand v.callee v.suffix))
      (Spec.Cmac.aesInitContract X86.abi 2376) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesInitSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesInitPre X86.abi.ptrBits) (post := Spec.Cmac.aesInitPost X86.abi.ptrBits)
    (wa := false) (stack := 52) (bytes := 2324) (init_verified v) (by decide) (init_noEsp v)
    (init_stackUse v) (initPre_local _) (initPost_local _) (fun vs m m₁ m₂ r hl _ => initPostOut_local _ vs m m₁ m₂ r hl) initFrameSat_pre

theorem absorb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2336 6 (absorb v.callee v.suffix))
      (Spec.Cmac.aesAbsorbContract X86.abi 2396) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesAbsorbSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesAbsorbPre X86.abi.ptrBits) (post := Spec.Cmac.aesAbsorbPost X86.abi.ptrBits)
    (wa := false) (stack := 60) (bytes := 2336) (absorb_verified v) (by decide) (absorb_noEsp v)
    (absorb_stackUse v) (absorbPre_local _) (absorbPost_local _) (fun vs m m₁ m₂ r hl _ => absorbPostOut_local _ vs m m₁ m₂ r hl) absorbFrameSat_pre

theorem finish_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 2332 5 (finish v.callee v.suffix))
      (Spec.Cmac.aesFinishContract X86.abi 2392) :=
  X86.Verified.stackScratch (sig := Spec.Cmac.aesFinishSig) (nm := "scratch") (e := .u64) (n := 288)
    (pre := Spec.Cmac.aesFinishPre X86.abi.ptrBits) (post := Spec.Cmac.aesFinishPost X86.abi.ptrBits)
    (wa := false) (stack := 60) (bytes := 2332) (finish_verified v) (by decide) (finish_noEsp v)
    (finish_stackUse v) (finishPre_local _) (finishPost_local _) (fun vs m m₁ m₂ r hl _ => finishPostOut_local _ vs m m₁ m₂ r hl) finishFrameSat_pre

end VG.Proof.CmacAes.Stream.X86

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86

/-- The frame of `withStackScratch` keeps the stack pointer for any `c` that
does, if it does for an empty body (decided for literal sizes). -/
theorem withStackScratch_spSafe {bytes n : Nat} {c : Prog isa}
    (h : c.all (fun i => !isa.writesSp i) = true)
    (hf : (Impl.StackScratch.X86.withStackScratch bytes n (.block [])).all
      (fun i => !isa.writesSp i) = true := by decide) :
    (Impl.StackScratch.X86.withStackScratch bytes n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.StackScratch.X86.withStackScratch, Code.all, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at hf ⊢
  simp_all

end VG.Proof.CmacAes.Stream.X86
