module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Lay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! ### `RsaPkcs1Sig.X86.Wrap`, which this module and modules that import it used -/

section

/-!
# The frames of the x86 RSA padding functions: correctness and constant time

`wrap_ok`: the body runs from `entered F s`, the state after the push and
the allocation; if it changes memory only within regions apart from the
push (`saveRegion`) and the return address (`retRegion`), the function returns with the
calling convention's registers, stack pointer and return address, and its
result and memory as the body left them. `wrap_ct`: two runs with the same
stack pointer leak the same trace if the body's runs from the entered
states do.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86

/-- What the frame's size must be. -/
abbrev FrameOk (F : Nat) : Prop := 0 < F ∧ F < 4096 ∧ F % 4 = 0

/-- The state the body starts in: after the push and the allocation. -/
def entered (F : Nat) (s : State) : State := allocFrame F (pushed savedRegs s)

/-- The push's 16 bytes below the stack pointer on entry. -/
abbrev saveRegion (s : State) : Region := ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩

/-- The return address. -/
abbrev retRegion (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

theorem entered_esp (F : Nat) (s : State) :
    (entered F s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 F := by
  simp only [entered, allocFrame_esp, pushed_esp]; rfl

theorem entered_rd (F : Nat) (s : State) : (entered F s).rd = s.rd := by simp [entered]

theorem entered_wr (F : Nat) (s : State) :
    (entered F s).wr = ⟨(s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 F).setWidth 64, F⟩ ::
      ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ :: s.wr := by
  simp only [entered, allocFrame_wr, pushed_wr, pushed_esp]; rfl

theorem entered_mem (F : Nat) (s : State) : (entered F s).mem = (pushed savedRegs s).mem := rfl

theorem pushRegs_noSp : Reg.esp ∉ savedRegs := by decide

theorem restore_noSp : NoSp (.block restoreRegs : Prog isa) := NoSp.of_all (by decide)

/-- The word `i` of the push, read through `esp` after it. -/
theorem push_word {s : State} (hsp : 16 ≤ (s.gpr .esp).toNat) {i : Nat} (hi : i < 4) :
    (pushed savedRegs s).mem.readW (addr ((pushed savedRegs s).gpr .esp) (4 * i)) 32 =
      s.gpr (savedRegs[3 - i]'(by simp only [savedRegs, List.length_cons, List.length_nil]; omega_using [])) :=
  pushed_word pushRegs_noSp (by simpa [savedRegs] using hsp) (by simpa [savedRegs] using hi)

theorem restore_ok (t : State) (hr : ∀ d < 12, d % 4 = 0 → InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) d) 4) :
    WP isa (.block restoreRegs) t fun u =>
      u.gpr .edi = t.mem.readW (addr (t.gpr .esp) 0) 32 ∧
      u.gpr .esi = t.mem.readW (addr (t.gpr .esp) 4) 32 ∧
      u.gpr .ebp = t.mem.readW (addr (t.gpr .esp) 8) 32 ∧
      u.gpr .esp = t.gpr .esp ∧ u.gpr .eax = t.gpr .eax ∧ u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr := by
  unfold restoreRegs
  refine wp_ldm rfl (hr 0 (by decide) rfl) fun a A => ?_
  refine wp_ldm (B := t.gpr .esp) (A.other .esp (by decide))
    (by rw [A.rd, A.wr]; exact hr 4 (by decide) rfl) fun b B => ?_
  refine wp_ldm (B := t.gpr .esp) (by rw [B.other .esp (by decide), A.other .esp (by decide)])
    (by rw [B.rd, B.wr, A.rd, A.wr]; exact hr 8 (by decide) rfl) fun c C => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [C.other .edi (by decide), B.other .edi (by decide), A.gpr]
  · rw [C.other .esi (by decide), B.gpr, A.mem]
  · rw [C.gpr, B.mem, A.mem]
  · rw [C.other .esp (by decide), B.other .esp (by decide), A.other .esp (by decide)]
  · rw [C.other .eax (by decide), B.other .eax (by decide), A.other .eax (by decide)]
  · rw [C.mem, B.mem, A.mem]
  · rw [C.rd, B.rd, A.rd]
  · rw [C.wr, B.wr, A.wr]

/-- `pop ebx` four times: `ebx` is the fourth word. -/
theorem popped_ebx (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW (addr (s.gpr .esp) 12) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

/-- Code that never writes `esp` keeps it, and its permissions. -/
theorem WP.rdwrSp {c : Prog isa} (hc : NoSp c) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .esp = s.gpr .esp := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, (Exec.rdwr he).1, (Exec.rdwr he).2, Exec.gpr hc he⟩

theorem wrap_ok {F : Nat} (hF : FrameOk F) {body : Prog isa} (hbs : NoSp body) {s : State}
    (hsp : 16 + F ≤ (s.gpr .esp).toNat) (hfit : (s.gpr .esp).toNat + 4 ≤ 2 ^ 32)
    {W : List Region} (hW : ∀ r ∈ W, (saveRegion s).Disjoint r ∧ (retRegion s).Disjoint r) {Q : BitVec 32 → Mem → Prop}
    (hb : WP isa body (entered F s) fun u => Frame W (entered F s).mem u.mem ∧ Q (u.gpr .eax) u.mem)
    (hQ : ∀ ax m m', Frame [below (s.gpr .esp) (16 + F)] m m' → Q ax m → Q ax m') :
    WP isa (wrap F body) s fun t => abiPreserved s t ∧ Q (t.gpr .eax) t.mem := by
  have h16 : 16 ≤ (s.gpr .esp).toNat := by omega_using [hsp]
  have pE : ((pushed savedRegs s).gpr .esp).toNat = (s.gpr .esp).toNat - 16 := by
    rw [pushed_esp]; exact sub_toNat (by simpa [savedRegs] using h16)
  have hinner : NoSp (.seq (.frame (.alloc F) body (.free F)) (.block restoreRegs) : Prog isa) := by
    intro i hi
    simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | hi) | rfl) | hi
    · rfl
    · exact hbs i hi
    · rfl
    · exact restore_noSp i hi
  -- What the releases may change: the frame and the push, `16 + F` bytes below `esp`.
  have hsub16 : Region.Sub (below (s.gpr .esp) (4 * savedRegs.length)) (below (s.gpr .esp) (16 + F)) :=
    below_sub (by simp only [savedRegs, List.length_cons, List.length_nil]; omega_using []) hsp
  have hsubF : Region.Sub (below ((pushed savedRegs s).gpr .esp) F) (below (s.gpr .esp) (16 + F)) := by
    rw [pushed_esp]; exact below_inner (by simp only [savedRegs, List.length_cons, List.length_nil]; omega_using []) hsp
  have retBelow : ∀ q ∈ [below (s.gpr .esp) (4 * savedRegs.length)], (retRegion s).Disjoint q := by
    intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    simp only [below, savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_using [hsp])]
    exact Offset.base_disjoint_below _ (n := 16) (k := 4) (by omega_using [])
  unfold wrap
  refine WP.frameLocal (by decide) pushRegs_noSp (by decide) (by simpa [savedRegs] using h16) hinner
    (fun t m _ ⟨abi, q⟩ fl => ⟨⟨abi.1, by
      show m.readW _ _ = _
      rw [fl.readW (r := retRegion s) (Region.contains_self _ _) retBelow (by decide)]
      exact abi.2⟩, hQ _ _ _ (fl.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact hsub16⟩) q⟩) ?_
  refine WP.seq ?_
  refine WP.frameAlloc hF.1 hF.2.1 hF.2.2 (by omega_using [hsp, pE]) hbs ?_
  refine WP.mono (WP.rdwrSp hbs hb) ?_
  rintro u0 ⟨⟨frame0, result0⟩, rdU, wrU, spU⟩ mm uu fl
  -- The alloc frame is apart from the push and the return address.
  have hW' : ∀ r ∈ W ++ [below ((pushed savedRegs s).gpr .esp) F],
      (saveRegion s).Disjoint r ∧ (retRegion s).Disjoint r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hW r hr
    · rw [List.mem_singleton.mp hr]
      refine ⟨?_, ?_⟩
      · rw [pushed_esp]
        show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩
          ⟨((s.gpr .esp - BitVec.ofNat 32 16) - BitVec.ofNat 32 F).setWidth 64, F⟩
        rw [Taint.sub_setWidth (show F ≤ (s.gpr .esp - BitVec.ofNat 32 16).toNat by
          rw [sub_toNat h16]; omega_using [hsp])]
        exact (Offset.below_disjoint _ (by omega_using [hF.2.1])).symm
      · refine Region.Disjoint.sub_right ?_ hsubF
        show Region.Disjoint _ ⟨(s.gpr .esp - BitVec.ofNat 32 (16 + F)).setWidth 64, 16 + F⟩
        rw [Taint.sub_setWidth hsp]
        exact (Offset.below_disjoint _ (by omega_using [hF.2.1])).symm
  have frame : Frame (W ++ [below ((pushed savedRegs s).gpr .esp) F]) (entered F s).mem
      ({ u0 with mem := mm, unknowns := uu } : State).mem :=
    (frame0.mono fun r hr => List.mem_append_left _ hr).trans
      (fl.mono fun r hr => List.mem_append_right _ hr)
  have result : Q (({ u0 with mem := mm, unknowns := uu } : State).gpr .eax)
      ({ u0 with mem := mm, unknowns := uu } : State).mem :=
    hQ _ _ _ (fl.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact hsubF⟩) result0
  replace rdU : ({ u0 with mem := mm, unknowns := uu } : State).rd = _ := rdU
  replace wrU : ({ u0 with mem := mm, unknowns := uu } : State).wr = _ := wrU
  replace spU : ({ u0 with mem := mm, unknowns := uu } : State).gpr .esp = _ := spU
  show WP isa _ (freed F ({ u0 with mem := mm, unknowns := uu } : State)) _
  generalize ({ u0 with mem := mm, unknowns := uu } : State) = u at frame result rdU wrU spU ⊢
  have spF : (freed F u).gpr .esp = (pushed savedRegs s).gpr .esp := by
    rw [freed_esp, spU, allocFrame_esp]; exact BitVec.sub_add_cancel _ _
  have wrF : (freed F u).wr = (pushed savedRegs s).wr := by
    rw [freed_wr, wrU, allocFrame_wr]; rfl
  have pfit : ((pushed savedRegs s).gpr .esp).toNat + 20 ≤ 2 ^ 32 := by omega_using [hfit, pE]
  have top : (saveRegion s).base = ((pushed savedRegs s).gpr .esp).setWidth 64 := by
    rw [pushed_esp]; rfl
  have topAddr : ∀ d < 20, addr ((pushed savedRegs s).gpr .esp) d = (saveRegion s).base + BitVec.ofNat 64 d := by
    intro d hd; rw [top]; exact addr_eq (by omega_using [pfit, hd])
  have read : ∀ d < 12, d % 4 = 0 → InRegions ((freed F u).rd ++ (freed F u).wr) (addr ((freed F u).gpr .esp) d) 4 := by
    intro d hd _
    rw [wrF, spF, pushed_wr, topAddr d (by omega_using [hd])]
    refine ⟨_, List.mem_append_right _ List.mem_cons_self, ?_⟩
    have e : (s.gpr .esp - BitVec.ofNat 32 (4 * savedRegs.length)).setWidth 64 = (saveRegion s).base := rfl
    simp only [below, e]
    exact Offset.contains_base _ (by simp only [savedRegs, List.length_cons, List.length_nil]; omega_using [hd]) (by omega_using [hd])
  have entW : ∀ d < 16, d % 4 = 0 → u.mem.readW (addr ((pushed savedRegs s).gpr .esp) d) 32 =
      (pushed savedRegs s).mem.readW (addr ((pushed savedRegs s).gpr .esp) d) 32 := by
    intro d hd _
    rw [topAddr d (by omega_using [hd])]
    exact frame.readW (r := saveRegion s) (Offset.contains_base _ (by omega_arith) (by omega_using [hd]))
      (fun r hr => (hW' r hr).1) (by decide)
  refine WP.mono (restore_ok (freed F u) read) ?_
  rintro t ⟨edi, esi, ebp, spT, eaxT, memT, -, -⟩
  have words : ∀ i < 4, t.mem.readW (addr (t.gpr .esp) (4 * i)) 32 =
      s.gpr (savedRegs[3 - i]'(by simp only [savedRegs, List.length_cons, List.length_nil]; omega_using [])) := by
    intro i hi
    rw [memT, freed_mem, spT, spF, entW (4 * i) (by omega_using [hi]) (by omega_using [])]
    exact push_word h16 hi
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · show (popped .ebx 4 t).gpr .ebx = _
      rw [popped_ebx]; exact words 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), esi, freed_mem, spF,
        entW 4 (by decide) (by decide)]; exact push_word h16 (i := 1) (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), edi, freed_mem, spF,
        entW 0 (by decide) (by decide)]; exact push_word h16 (i := 0) (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide), ebp, freed_mem, spF,
        entW 8 (by decide) (by decide)]; exact push_word h16 (i := 2) (by decide)
    · rw [popped_esp, spT, spF, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, memT, freed_mem]
    rw [frame.readW (r := retRegion s) (Region.contains_self _ _) (fun r hr => (hW' r hr).2) (by decide)]
    rw [entered_mem]
    refine (pushed_frame pushRegs_noSp (by simpa [savedRegs] using h16)).readW
      (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    simp only [below, savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_using [hsp])]
    exact Offset.base_disjoint_below _ (n := 16) (k := 4) (by omega_using [])
  · rw [popped_gpr _ _ _ (by decide) (by decide), popped_mem, eaxT, memT, freed_mem,
      freed_gpr _ _ (by decide)]
    exact result

/-- Code that never writes `esp` ends both runs with the same `esp` if they
start with the same. -/
theorem RelCT.keepSp {P Q : State → State → Prop} {c : Prog isa} (hc : NoSp c)
    (hp : ∀ a b, P a b → a.gpr .esp = b.gpr .esp) (h : RelCT isa P c Q) :
    RelCT isa P c fun a b => Q a b ∧ a.gpr .esp = b.gpr .esp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨tr, q⟩ := h s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  exact ⟨tr, q, by rw [Exec.gpr hc e₁, Exec.gpr hc e₂]; exact hp _ _ hP⟩

theorem restore_relCT : RelCT isa (fun a b => a.gpr .esp = b.gpr .esp) (.block restoreRegs) fun _ _ => True :=
  RelCT.taint (A := taint) (τr [.esp]) (fun _ _ h => agree_regs (by simpa using h)) (by taint_decide)

/-- Two runs of the frames leak the same trace if they have the same stack
pointer, room for the frames, and the body's runs from the entered states
leak the same trace. -/
theorem wrap_ct {F : Nat} {body : Prog isa} (hbs : NoSp body) {P : State → State → Prop}
    (hsp : ∀ s t, P s t → s.gpr .esp = t.gpr .esp)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = entered F s ∧ b = entered F t) body fun _ _ => True) :
    RelCT isa P (wrap F body) fun _ _ => True := by
  unfold wrap
  refine RelCT.frame (R := fun _ _ => True) hsp ?_
  have alloc : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = pushed savedRegs s₁ ∧ b = pushed savedRegs s₂)
      (.frame (.alloc F) body (.free F)) fun a b => a.gpr .esp = b.gpr .esp := by
    have hn : NoSp (.frame (.alloc F) body (.free F) : Prog isa) := by
      intro i hi
      simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
      rcases hi with (rfl | hi) | rfl
      · rfl
      · exact hbs i hi
      · rfl
    refine (RelCT.keepSp hn ?_ (RelCT.frameAlloc (R := fun _ _ => True) ?_)).mono (fun _ _ h => h)
      fun _ _ h => h.2
    · rintro a b ⟨s₁, s₂, h, rfl, rfl⟩
      rw [pushed_esp, pushed_esp, hsp _ _ h]
    · refine hb.mono ?_ fun _ _ h => h
      rintro a b ⟨_, _, ⟨s₁, s₂, h, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨s₁, s₂, h, rfl, rfl⟩
  exact RelCT.seq alloc restore_relCT

end VG.Proof.RsaPkcs1Sig.X86

end

end

/-!
# The x86 RSA padding functions: the layout on entry

`layOf F argv ro rw s C`: the layout of a function whose entry state is
`s`, with a frame of `F` bytes, the arguments `argv`, the buffers `ro` it
only reads and `rw` it writes, and `C` bytes below the frame for its calls.
`ok_entered`: from what the calling convention and a contract give on entry,
the state the body starts in (`entered F s`, `Proof/RsaPkcs1Sig/X86/Entry.lean`)
has that layout. Every address of the layout is `esp`, on entry, plus or
minus an offset, without wrapping around (`fr_toNat`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86

/-- The layout of a function entered in `s`. -/
def layOf (F : Nat) (argv : List (BitVec 32)) (ro rw : List Region) (s : State) (C : Nat) : Lay where
  B := s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 F
  F := F
  argv := argv
  ro := ro
  rw := rw
  C := C

section
variable {F C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

theorem layOf_B_toNat (hsp : 16 + F ≤ (s.gpr .esp).toNat) :
    (layOf F argv ro rw s C).B.toNat = (s.gpr .esp).toNat - 16 - F := by
  simp only [layOf]
  rw [sub_toNat (by rw [sub_toNat (by omega_using [hsp])]; omega_using [hsp]), sub_toNat (by omega_using [hsp])]

theorem fr_toNat' (hsp : 16 + F ≤ (s.gpr .esp).toNat) {d : Nat} (hd : (s.gpr .esp).toNat + d < 2 ^ 32 + 16 + F) :
    ((layOf F argv ro rw s C).fr d).toNat = (s.gpr .esp).toNat - 16 - F + d := by
  have hB := layOf_B_toNat (argv := argv) (ro := ro) (rw := rw) (C := C) hsp
  simp only [Lay.fr, Lay.Q]
  rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hB,
    Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat - 16 - F) (by have := (s.gpr .esp).isLt; omega_using []),
    Nat.mod_eq_of_lt (a := d) (by omega_using [hsp, hd])]
  exact Nat.mod_eq_of_lt (by omega_using [hsp, hd])

theorem esp64_toNat (s : State) : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])

/-- `ok_entered`, of an entry whose permissions include the layout's. -/
theorem ok_entered_of {S : Nat} (hS : S = C + 16 + F) (hF : FrameOk F) (hsp : S ≤ (s.gpr .esp).toNat)
    (hn : 0 < argv.length)
    (hfit : (s.gpr .esp).toNat + 4 + 4 * argv.length ≤ 2 ^ 32)
    (hrd : ∀ r ∈ ro, r ∈ s.rd) (hwr : ∀ r ∈ rw, r ∈ s.wr)
    (hargsW : ∃ k, 4 * argv.length ≤ k ∧ (⟨argAddr s 0, k⟩ : Region) ∈ s.wr)
    (hstk : ∀ r ∈ ro ++ rw,
      (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 S, S⟩ : Region).Disjoint r)
    (hret : ∀ r ∈ rw, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (hwro : ∀ w ∈ rw, ∀ r ∈ ro ++ [⟨argAddr s 0, 4 * argv.length⟩], w.Disjoint r)
    (hwrw : rw.Pairwise Region.Disjoint) (hfits : ∀ r ∈ ro ++ rw, r.base.toNat + r.len ≤ 2 ^ 32)
    (hargs : ∀ j < argv.length, arg s j = argv.getD j 0) :
    (layOf F argv ro rw s C).Ok (entered F s) := by
  subst hS
  have hE := (s.gpr .esp).isLt
  have h16 : 16 + F ≤ (s.gpr .esp).toNat := by omega
  have hB := layOf_B_toNat (argv := argv) (ro := ro) (rw := rw) (C := C) h16
  have e64 := esp64_toNat s
  -- Every address of the layout is `esp` on entry plus or minus an offset.
  have hQ : (layOf F argv ro rw s C).Q = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (16 + F) := by
    simp only [Lay.Q, layOf]
    rw [Taint.sub_setWidth (by rw [sub_toNat (by omega_using [hsp])]; omega_using [hsp]), Taint.sub_setWidth (by omega_using [hsp]),
      BitVec.sub_sub, BitVec.ofNat_add]
  have hfr : ∀ d, (layOf F argv ro rw s C).fr d =
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (16 + F) + BitVec.ofNat 64 d := by
    intro d; simp only [Lay.fr]; rw [hQ]
  have up : ∀ d, d ≤ 4 + 4 * argv.length →
      (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (16 + F) + BitVec.ofNat 64 (16 + F + d) =
        (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 d := by
    intro d _
    rw [show BitVec.ofNat 64 (16 + F + d) = BitVec.ofNat 64 (16 + F) + BitVec.ofNat 64 d from
      BitVec.ofNat_add _ _, ← BitVec.add_assoc, BitVec.sub_add_cancel]
  have argAddrJ : ∀ j < argv.length, argAddr s j = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * j) := by
    intro j hj
    apply BitVec.eq_of_toNat_eq
    rw [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, e64, Nat.mod_eq_of_lt (a := 4 + 4 * j) (by omega_using [hfit, hj]),
      Nat.mod_eq_of_lt (a := 4 + 4 * j) (by omega_using [hfit, hj]),
      Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat + (4 + 4 * j)) (by omega_using [hfit, hj]), Nat.mod_eq_of_lt (by omega_using [hfit, hj])]
  have argA : ∀ j < argv.length, (layOf F argv ro rw s C).argA j = argAddr s j := by
    intro j hj
    simp only [Lay.argA, Impl.RsaPkcs1Sig.X86.argOff]
    rw [hfr]
    simp only [layOf]
    rw [show F + 20 + 4 * j = 16 + F + (4 + 4 * j) by omega_using [], up _ (by omega_using [hj]), argAddrJ j hj]
  have argAddr0 : argAddr s 0 = (layOf F argv ro rw s C).fr (F + 20) := by
    have := argA 0 hn
    simp only [Lay.argA, Impl.RsaPkcs1Sig.X86.argOff, Nat.mul_zero, Nat.add_zero] at this
    exact this.symm
  refine
    { sp := ?_, rd := ?_, wr := ?_, argsW := ?_, BC := ?_, fit := ?_, stk := ?_, ret := ?_, wro := ?_,
      wrw := hwrw, fits := hfits, args := ?_ }
  · rw [entered_esp]; rfl
  · rw [entered_rd]; exact hrd
  · have hsave : (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 = (layOf F argv ro rw s C).fr F := by
      rw [hfr, Taint.sub_setWidth (by omega_using [hsp])]
      try simp only [layOf]
      rw [show BitVec.ofNat 64 (16 + F) = BitVec.ofNat 64 16 + BitVec.ofNat 64 F from BitVec.ofNat_add _ _,
        ← BitVec.sub_sub, BitVec.sub_add_cancel]
    rw [entered_wr, hsave]
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hwr r hr))
  · obtain ⟨k, hk, hm⟩ := hargsW
    refine ⟨k, hk, ?_⟩
    show (⟨(layOf F argv ro rw s C).fr (F + 20), k⟩ : Region) ∈ _
    rw [entered_wr, ← argAddr0]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm)
  · show C ≤ (layOf F argv ro rw s C).B.toNat
    rw [hB]; omega_using [hsp]
  · show (layOf F argv ro rw s C).B.toNat + F + 20 + 4 * argv.length ≤ 2 ^ 32
    rw [hB]; omega_using [hfit, hsp]
  · intro r hr
    have e : (layOf F argv ro rw s C).STK =
        ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (C + 16 + F), C + 16 + F⟩ := by
      simp only [Lay.STK]
      rw [hQ, BitVec.sub_sub, ← BitVec.ofNat_add]
      simp only [layOf, Region.mk.injEq]
      exact ⟨by rw [show 16 + F + C = C + 16 + F by omega_using []], by omega_using []⟩
    rw [e]; exact hstk r hr
  · intro r hr
    have e : (layOf F argv ro rw s C).RET = ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
      simp only [Lay.RET]
      rw [hfr]
      simp only [layOf]
      rw [show F + 16 = 16 + F + 0 by omega_using [], up 0 (by omega_using []), BitVec.add_zero]
    rw [e]; exact hret r hr
  · intro w hw r hr
    refine hwro w hw r ?_
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · simp only [List.mem_singleton] at hr; subst hr
      refine List.mem_append_right _ ?_
      simp only [Lay.ARGS, Lay.A, List.mem_singleton]
      rw [argAddr0]; rfl
  · intro j hj
    replace hj : j < argv.length := hj
    have hpush : Frame [below (s.gpr .esp) (4 * Impl.RsaPkcs1Sig.X86.savedRegs.length)] s.mem
        (pushed Impl.RsaPkcs1Sig.X86.savedRegs s).mem :=
      pushed_frame (by decide) (by simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_using [hsp])
    rw [argA j hj, entered_mem]
    refine (hpush.readW (r := ⟨argAddr s j, 4⟩) (Region.contains_self _ _) ?_ (by decide)).trans (hargs j hj)
    intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    simp only [below, Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega_using [hsp]), argAddrJ j hj]
    exact Offset.disjoint_below _ (by omega_using [hfit, hj])


theorem ok_entered {S : Nat} (hS : S = C + 16 + F) (hF : FrameOk F) (hsp : S ≤ (s.gpr .esp).toNat)
    (hn : 0 < argv.length)
    (hfit : (s.gpr .esp).toNat + 4 + 4 * argv.length ≤ 2 ^ 32)
    (hrd : s.rd = ro) (hwr : s.wr = rw ++ [⟨argAddr s 0, 4 * argv.length⟩])
    (hstk : ∀ r ∈ ro ++ rw,
      (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 S, S⟩ : Region).Disjoint r)
    (hret : ∀ r ∈ rw, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (hwro : ∀ w ∈ rw, ∀ r ∈ ro ++ [⟨argAddr s 0, 4 * argv.length⟩], w.Disjoint r)
    (hwrw : rw.Pairwise Region.Disjoint) (hfits : ∀ r ∈ ro ++ rw, r.base.toNat + r.len ≤ 2 ^ 32)
    (hargs : ∀ j < argv.length, arg s j = argv.getD j 0) :
    (layOf F argv ro rw s C).Ok (entered F s) :=
  ok_entered_of hS hF hsp hn hfit (fun _ hr => hrd ▸ hr) (fun _ hr => hwr ▸ List.mem_append_left _ hr)
    ⟨_, Nat.le_refl _, hwr ▸ List.mem_append_right _ (List.mem_singleton_self _)⟩ hstk hret hwro hwrw hfits hargs

end

section
variable {F C : Nat} {argv : List (BitVec 32)} {ro rw : List Region} {s : State}

/-- What the releases of the frame and the push may change, the `16 + F`
bytes below `esp` on entry, is within the layout's stack. -/
theorem release_stk :
    Region.Sub (below (s.gpr .esp) (16 + F)) (layOf F argv ro rw s C).STK := by
  have e : s.gpr .esp - BitVec.ofNat 32 (16 + F) = (layOf F argv ro rw s C).B := by
    show _ = s.gpr .esp - BitVec.ofNat 32 16 - BitVec.ofNat 32 F
    rw [BitVec.sub_sub, BitVec.ofNat_add]
  have := Lay.sub_stk (L := layOf F argv ro rw s C) (d := 0) (n := 16 + F)
    (by show 0 + (16 + F) ≤ F + 16; omega_using [])
  simp only [Lay.fr, BitVec.add_zero] at this
  show Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 (16 + F)).setWidth 64, 16 + F⟩ _
  rw [e]; exact this

/-- `release_stk`, for a frame. -/
theorem release_frame {m m' : Mem}
    (fl : Frame [below (s.gpr .esp) (16 + F)] m m') : Frame [(layOf F argv ro rw s C).STK] m m' :=
  fl.sub fun q hq => ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hq]; exact release_stk⟩

/-- The push's bytes are the layout's saved registers. -/
theorem save_eq (hsp : 16 + F ≤ (s.gpr .esp).toNat) : saveRegion s = (layOf F argv ro rw s C).SAVE := by
  have := (s.gpr .esp).isLt
  have h := fr_toNat' (argv := argv) (ro := ro) (rw := rw) (C := C) hsp (d := F) (by omega_using [])
  simp only [saveRegion, Lay.SAVE]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show (layOf F argv ro rw s C).F = F from rfl, h, BitVec.toNat_setWidth, sub_toNat (by omega_using [hsp]),
    Nat.mod_eq_of_lt (by omega_using [])]
  omega_using [hsp]

/-- The return address is the layout's. -/
theorem ret_eq (hsp : 16 + F ≤ (s.gpr .esp).toNat) : retRegion s = (layOf F argv ro rw s C).RET := by
  have := (s.gpr .esp).isLt
  have h := fr_toNat' (argv := argv) (ro := ro) (rw := rw) (C := C) hsp (d := F + 16) (by omega_using [])
  simp only [retRegion, Lay.RET]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [show (layOf F argv ro rw s C).F = F from rfl, h, esp64_toNat]
  omega_using [hsp]

/-- A buffer only read has the same bytes on entry to the body. -/
theorem entered_ro (hsp : 16 + F ≤ (s.gpr .esp).toNat) (h : (layOf F argv ro rw s C).Ok (entered F s))
    {R : Region} (hR : R ∈ ro) :
    Spec.Rsa.bytesAt (entered F s).mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have hf : Frame [saveRegion s] s.mem (entered F s).mem := by
    rw [entered_mem]
    have := pushed_frame (s := s) pushRegs_noSp
      (by simp only [Impl.RsaPkcs1Sig.X86.savedRegs, List.length_cons, List.length_nil]; omega_using [hsp])
    simpa [Impl.RsaPkcs1Sig.X86.savedRegs, below] using this
  refine Proof.RsaPkcs1Sig.bytesAt_frame hf (fun r hr => ?_) (by have := h.fits R (List.mem_append_left _ hR); omega_using [this])
  simp only [List.mem_singleton] at hr; subst hr
  rw [save_eq (argv := argv) (ro := ro) (rw := rw) (C := C) hsp]
  exact ((h.stk R (List.mem_append_left _ hR)).sub_left (Lay.sub_stk (by simp only [layOf]; omega_using []))).symm

end

end VG.Proof.RsaPkcs1Sig.X86
