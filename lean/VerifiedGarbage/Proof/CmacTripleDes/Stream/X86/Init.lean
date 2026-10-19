module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Common
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Inline
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Common
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
import VerifiedGarbage.Proof.CmacTripleDes.X86.FinalizeCorrect
import VerifiedGarbage.Proof.CmacTripleDes.X86.Init
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.CmacTripleDes.InlineCT
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.X86.Inline
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Finalize
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.FinalizeCorrect
meta import VerifiedGarbage.Proof.CmacTripleDes.X86.Init
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Streaming TDEA-CMAC on x86: `vg_cmac_triple_des_stream_init`

The code keeps `ebx` in the chaining value's place, runs `init` with the
state as its `out` (which writes the key schedule and the subkeys before
it), restores `ebx` and zeroes the chaining value: the state then
represents the empty message. The code around the run of `init` is constant
time by the taint analysis (from `esp` and the stack arguments), and the run
by `init`'s own proof (`init_rel`), its arguments pinned by `IMid₁`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.X86

open VG VG.X86 VG.Impl.CmacTripleDes.Stream.X86
open VG.Impl.CmacTripleDes.X86 (at_)
open VG.Proof.MdStream.X86 (Upd Mupd wp_movi wp_movm wp_store)
open VG.Proof.CmacTripleDes.X86 (ea_at')

section
variable (s₀ : State)

abbrev iSt : BitVec 32 := arg s₀ 0
abbrev iKp : BitVec 32 := arg s₀ 1
abbrev iKL : Nat := (arg s₀ 2).toNat
abbrev iSc : BitVec 32 := arg s₀ 3
abbrev iE : BitVec 32 := s₀.gpr .esp
abbrev istR : Region := ⟨(iSt s₀).setWidth 64, 416⟩
abbrev ikR : Region := ⟨(iKp s₀).setWidth 64, iKL s₀⟩
abbrev iscR : Region := ⟨(iSc s₀).setWidth 64, 640⟩
abbrev iaR : Region := ⟨argAddr s₀ 0, 16⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev IBig : List Region := [istR s₀, iscR s₀, below (iE s₀) 20]

/-- The memory with `ebx` kept in the chaining value's place. -/
def iMem : Mem := s₀.mem.writeW ((iSt s₀).setWidth 64 + BitVec.ofNat 64 400) (s₀.gpr .ebx)

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
  b_st' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint (istR s₀)
  b_k' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint (ikR s₀)
  b_s' : (⟨(iE s₀).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint (iscR s₀)
  fSt : (iSt s₀).toNat + 416 ≤ 2 ^ 32
  fK : (iKp s₀).toNat + iKL s₀ ≤ 2 ^ 32
  fS : (iSc s₀).toNat + 640 ≤ 2 ^ 32
  esp20 : 20 ≤ (iE s₀).toNat
  espfit : (iE s₀).toNat + 20 ≤ 2 ^ 32
  klen : Spec.TripleDes.validKey (iKL s₀)

theorem IPre.of {s₀ : State} (h : initX86.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

namespace IPre
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem b_st : (below (iE s₀) 20).Disjoint (istR s₀) := by rw [below_eq hp.esp20]; exact hp.b_st'
theorem b_k : (below (iE s₀) 20).Disjoint (ikR s₀) := by rw [below_eq hp.esp20]; exact hp.b_k'
theorem b_s : (below (iE s₀) 20).Disjoint (iscR s₀) := by rw [below_eq hp.esp20]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.espfit; omega

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
    · exact (args_below hp.fit (by decide) hp.esp20).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 4 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 16) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end IPre

theorem IPre.iMem_big {s₀ : State} (_hp : IPre s₀) : Frame (IBig s₀) s₀.mem (iMem s₀) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨istR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Before `init` -/

/-- What the code before `init` leaves. -/
structure IMid₁ (s₀ s : State) : Prop where
  args : IArgs s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀)
  esp : s.gpr .esp = iE s₀
  mem : s.mem = iMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa (.block initPre) s₀ (IMid₁ s₀) := by
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fSt' : (iSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have e20 := hp.esp20
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  refine wp_store (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400)
    (by rw [ea_at', u₁.gpr]; exact addr_eq (by omega))
    (by rw [u₁.wr, hp.wr]; exact ⟨istR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun s₂ v₂ => ?_
  have hm₂ : s₂.mem = iMem s₀ := by rw [v₂.mem, u₁.mem, u₁.other _ (by decide), iMem]
  have esp₂ : s₂.gpr .esp = iE s₀ := by rw [v₂.gpr, u₁.other _ (by decide)]
  have rd₂ : s₂.rd = s₀.rd := by rw [v₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [v₂.wr, u₁.wr]
  have av : ∀ i < 4, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [hm₂]; exact hp.keep hp.iMem_big hi
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rd₂, wr₂]; exact hp.arg_in (by decide)) (av 1 (by decide))
    fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂]; exact hp.arg_in (by decide)) (by rw [u₃.mem]; exact av 2 (by decide))
    fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem]; exact av 3 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have esp₅ : s₅.gpr .esp = iE s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, rd₂]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]
  have oSt : Region.Sub ⟨(iSt s₀).setWidth 64, 400⟩ (istR s₀) := Region.sub_prefix (by decide)
  refine ⟨?_, esp₅, by rw [u₅.mem, u₄.mem, u₃.mem, hm₂], rd₅, wr₅, fun r h1 h2 h3 h4 => by
    rw [u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, v₂.gpr, u₁.other _ h1]⟩
  exact
  { ebx := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    ecx := by rw [u₅.other _ (by decide), u₄.gpr]; exact arg_ofNat s₀ 2
    eax := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.gpr]
    edx := u₅.gpr
    klen := hp.klen
    esp := by rw [esp₅]; exact e20
    ko := (hp.st_k.sub_left oSt).symm
    ks := hp.k_s
    os := hp.st_s.sub_left oSt
    bK := by rw [esp₅]; exact hp.b_k
    bO := by rw [esp₅]; exact hp.b_st.sub_right oSt
    bS := by rw [esp₅]; exact hp.b_s
    fK := hp.fK
    fO := by omega
    fS := hp.fS
    reads := by
      rw [rd₅, wr₅, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨ikR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₅, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨istR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨iscR s₀, by simp, 0, by simp, by simp⟩ }

/-! ## After `init` -/

/-- What is known after `init`. -/
structure IAft (s₀ s : State) : Prop where
  esp : s.gpr .esp = iE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (IBig s₀) s₀.mem s.mem
  keep : ∀ r ∈ calleeSaved, r ≠ .ebx → s.gpr r = s₀.gpr r
  stash : s.mem.readW ((iSt s₀).setWidth 64 + BitVec.ofNat 64 400) 32 = s₀.gpr .ebx

theorem IAft.pt {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) : Pt 4 s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.keep h.frame hi⟩

theorem calleeSaved_ne : ∀ r ∈ calleeSaved, r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by decide

theorem IMid₁.after {s₀ s s' : State} (hp : IPre s₀) (h : IMid₁ s₀ s)
    (h' : IPost s (iKp s₀) (iSt s₀) (iSc s₀) (iKL s₀) s') : IAft s₀ s' := by
  have fr := h'.frame
  rw [h.esp, h.mem] at fr
  have fSt := hp.fSt
  refine ⟨by rw [h'.saved .esp (by simp [calleeSaved]), h.esp], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr],
    hp.iMem_big.trans (fr.sub fun r hr => ?_), fun r hr hb => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨istR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨iscR s₀, by simp, fun _ h => h⟩
    · exact ⟨below (iE s₀) 20, by simp, fun _ h => h⟩
  · obtain ⟨h1, h3, h4⟩ := calleeSaved_ne r hr
    rw [h'.saved r hr]; exact h.keep r h1 hb h3 h4
  · have sub : Region.Sub ⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 400, 4⟩ (istR s₀) :=
      Offset.sub_base _ (by decide)
    rw [fr.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact hp.st_s.sub_left sub
        · exact hp.b_st.symm.sub_left sub) (by decide), iMem, Mem.readW_writeW_self32]

/-! ## After `init` -/

/-- The memory after zeroing the chaining value at `p`, a word at a time. -/
def zeroCv (m : Mem) (p : Addr) : Mem :=
  (m.writeW p (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 4) (0 : BitVec 32)

theorem zeroCv_bytes (m : Mem) (p : Addr) : Spec.Aes.bytesAt (zeroCv m p) p 8 = Spec.Cmac.zeros 8 := by
  rw [zeroCv, ← Proof.Cmac.le8_readW, Proof.CmacTripleDes.readW64_split, Mem.readW_writeW_self32,
    Proof.CmacTripleDes.X86.readW_lo_of_hi]
  decide

theorem zeroCv_frame (m : Mem) (p : Addr) : Frame [⟨p, 8⟩] m (zeroCv m p) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    simpa using Offset.contains_base p (d := 0) (n := 4) (k := 8) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 4) (n := 4) (k := 8) (by decide) (by decide))

/-- `ebx` restored, and the chaining value zeroed. -/
theorem initPost_wp {s₀ s : State} (hp : IPre s₀) (h : IAft s₀ s) :
    WP isa (.block initPost) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧
      s'.mem = zeroCv s.mem ((iSt s₀).setWidth 64 + BitVec.ofNat 64 400) := by
  have fSt : (arg s₀ 0).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have fSt' : (iSt s₀).toNat + 416 ≤ 2 ^ 32 := hp.fSt
  have rw₀ : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have inSt (d : Nat) (hd : d + 4 ≤ 416) : InRegions s₀.wr ((iSt s₀).setWidth 64 + BitVec.ofNat 64 d) 4 := by
    rw [hp.wr]; exact ⟨istR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  refine wp_arg (s₀ := s₀) h.esp (by rw [rw₀]; exact hp.arg_in (by decide)) (hp.keep h.frame (by decide))
    fun s₁ u₁ => ?_
  refine wp_movm (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400)
    (by rw [ea_at', u₁.gpr]; exact addr_eq (by omega))
    (by
      rw [u₁.rd, u₁.wr, rw₀]
      obtain ⟨r, hr, hc⟩ := inSt 400 (by decide)
      exact ⟨r, List.mem_append_right _ hr, hc⟩) fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  have eax₃ : s₃.gpr .eax = iSt s₀ := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine wp_store (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400)
    (by rw [ea_at', eax₃]; exact addr_eq (by omega))
    (by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact inSt 400 (by decide)) fun s₄ v₄ => ?_
  refine wp_store (a := (iSt s₀).setWidth 64 + BitVec.ofNat 64 400 + BitVec.ofNat 64 4)
    (by rw [ea_at', v₄.gpr, eax₃, Offset.add_add]; exact addr_eq (by omega))
    (by rw [v₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr, Offset.add_add]; exact inSt 404 (by decide))
    fun s₅ v₅ => WP.block_nil ⟨fun r hr => ?_, ?_⟩
  · rw [v₅.gpr, v₄.gpr]
    by_cases hb : r = .ebx
    · subst hb
      rw [u₃.other _ (by decide), u₂.gpr, u₁.mem]; exact h.stash
    · obtain ⟨h1, h3, -⟩ := calleeSaved_ne r hr
      rw [u₃.other _ h3, u₂.other _ hb, u₁.other _ h1]; exact h.keep r hr hb
  · rw [v₅.mem, v₄.gpr, v₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, zeroCv]

/-! ## The whole function -/

theorem init_wp {s₀ : State} (h0 : initX86.pre s₀) :
    WP isa streamInit s₀ fun s' => abiPreserved s₀ s' ∧ initX86.post s₀ s' := by
  have hp := IPre.of h0
  have fSt := hp.fSt
  have e20 := hp.esp20
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (init_inline_wp h₁.args) fun s₂ h₂ => ?_)
  have a₂ := h₁.after hp h₂
  refine WP.mono (initPost_wp hp a₂) fun s₃ ⟨hcs, m₃⟩ => ?_
  have fz : Frame [⟨(iSt s₀).setWidth 64 + BitVec.ofNat 64 400, 8⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact zeroCv_frame _ _
  have F₃ : Frame (IBig s₀) s₀.mem s₃.mem := a₂.frame.trans (fz.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨istR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  refine ⟨⟨hcs, F₃.readW (r := ⟨(iE s₀).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_st
    · exact hp.ret_s
    · exact ret_below e20
  · show Spec.Cmac.tdesRepr s₃.mem ((iSt s₀).setWidth 64)
      (Spec.TripleDes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)) []
    rw [Proof.CmacTripleDes.Stream.repr_iff]
    have hkey : Spec.TripleDes.bytesAt s₁.mem ((iKp s₀).setWidth 64) (iKL s₀) =
        Spec.TripleDes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀) := by
      rw [h₁.mem]
      simp only [Spec.TripleDes.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 4)).bytes
        (R := ikR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_k.symm.sub_right (Offset.sub_base _ (by decide)))
        (by show iKL s₀ ≤ 2 ^ 64; have := hp.fK; omega) (List.mem_range.mp hi)
    have hlen : (Spec.TripleDes.bytesAt s₀.mem ((iKp s₀).setWidth 64) (iKL s₀)).length = iKL s₀ := by
      simp [Spec.TripleDes.bytesAt]
    obtain ⟨hs, hk⟩ := h₂.out
    rw [hkey] at hs hk
    refine ⟨⟨by rw [hlen]; exact hp.klen, ?_, ?_⟩, ?_, by
      simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]⟩
    · rw [Proof.CmacTripleDes.X86.scheduleAt_frame fz fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by decide) (by decide)]
      exact hs
    · rw [show (iSt s₀).setWidth 64 + 384 = (iSt s₀).setWidth 64 + BitVec.ofNat 64 384 from rfl,
        Proof.Cmac.bytesAt_frame fz (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
      exact hk
    · rw [show (iSt s₀).setWidth 64 + 400 = (iSt s₀).setWidth 64 + BitVec.ofNat 64 400 from rfl, m₃,
        zeroCv_bytes]
      rfl

/-! ## Constant time -/

theorem init_after {s₀ s : State} (hp : IPre s₀) (h : IMid₁ s₀ s) :
    WP isa initFrame s (IAft s₀) :=
  WP.mono (init_inline_wp h.args) fun _ h' => h.after hp h'

theorem streamInit_rel {s₀ s₀' : State} (h0 : initX86.pre s₀) (h0' : initX86.pre s₀')
    (hq : initX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamInit fun _ _ => True := by
  have hp := IPre.of h0
  have hp' := IPre.of h0'
  obtain ⟨qE, qa⟩ := hq
  have e0 : iSt s₀ = iSt s₀' := qa 0 (by decide)
  have e1 : iKp s₀ = iKp s₀' := qa 1 (by decide)
  have e2 : iKL s₀ = iKL s₀' := by rw [iKL, iKL, qa 2 (by decide)]
  have e3 : iSc s₀ = iSc s₀' := qa 3 (by decide)
  have ag : ∀ {a b : State}, Pt 4 s₀ a → Pt 4 s₀' b → VG.X86.Taint.Agree (argTaint [] (4 + 4 * 4)) a b :=
    fun h₁ h₂ => Pt.agree qE qa hp.argsOut hp'.argsOut h₁ h₂ fun r hr => by simp at hr
  have a := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') (argTaint [] (4 + 4 * 4))
    (fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ag (Pt.refl _ _) (Pt.refl _ _))
    (c := .block initPre) (by taint_decide)).wp (F₁ := IMid₁ s₀) (F₂ := IMid₁ s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨initPre_wp hp, initPre_wp hp'⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2
  have e := ((init_rel (E := iE s₀) (P := fun a b => IMid₁ s₀ a ∧ IMid₁ s₀' b) fun a b h =>
      ⟨h.1.args, by rw [e0, e1, e2, e3]; exact h.2.args, h.1.esp, by rw [h.2.esp]; exact qE.symm⟩).wp
      (F₁ := IAft s₀) (F₂ := IAft s₀') fun _ _ h => ⟨init_after hp h.1, init_after hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have p := RelCT.taint (A := taint) (P := fun a b => IAft s₀ a ∧ IAft s₀' b) (argTaint [] (4 + 4 * 4))
    (fun _ _ h => ag (h.1.pt hp) (h.2.pt hp')) (c := .block initPost) (by taint_decide)
  exact a.seq (e.seq p)

theorem init_ct : ConstantTime isa initX86.pre initX86.pub streamInit :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (streamInit_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.X86
