module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Call

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

theorem entered_gpr (F : Nat) (s : State) {r : Reg} (h : r ≠ .esp) : (entered F s).gpr r = s.gpr r := by
  simp only [entered]; rw [allocFrame_gpr _ _ h, pushed_gpr _ _ h]

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
      s.gpr (savedRegs[3 - i]'(by simp only [savedRegs, List.length_cons, List.length_nil]; omega)) :=
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
    (hb : WP isa body (entered F s) fun u => Frame W (entered F s).mem u.mem ∧ Q (u.gpr .eax) u.mem) :
    WP isa (wrap F body) s fun t => abiPreserved s t ∧ Q (t.gpr .eax) t.mem := by
  have h16 : 16 ≤ (s.gpr .esp).toNat := by omega
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
  unfold wrap
  refine WP.frame (by decide) pushRegs_noSp (by decide) (by simpa [savedRegs] using h16) hinner ?_
  refine WP.seq ?_
  refine WP.frameAlloc hF.1 hF.2.1 hF.2.2 (by omega) hbs ?_
  refine WP.mono (WP.rdwrSp hbs hb) ?_
  rintro u ⟨⟨frame, result⟩, rdU, wrU, spU⟩
  have spF : (freed F u).gpr .esp = (pushed savedRegs s).gpr .esp := by
    rw [freed_esp, spU, allocFrame_esp]; exact BitVec.sub_add_cancel _ _
  have wrF : (freed F u).wr = (pushed savedRegs s).wr := by
    rw [freed_wr, wrU, allocFrame_wr]; rfl
  have pfit : ((pushed savedRegs s).gpr .esp).toNat + 20 ≤ 2 ^ 32 := by omega
  have top : (saveRegion s).base = ((pushed savedRegs s).gpr .esp).setWidth 64 := by
    rw [pushed_esp]; rfl
  have topAddr : ∀ d < 20, addr ((pushed savedRegs s).gpr .esp) d = (saveRegion s).base + BitVec.ofNat 64 d := by
    intro d hd; rw [top]; exact addr_eq (by omega)
  have read : ∀ d < 12, d % 4 = 0 → InRegions ((freed F u).rd ++ (freed F u).wr) (addr ((freed F u).gpr .esp) d) 4 := by
    intro d hd _
    rw [wrF, spF, pushed_wr, topAddr d (by omega)]
    refine ⟨_, List.mem_append_right _ List.mem_cons_self, ?_⟩
    have e : (s.gpr .esp - BitVec.ofNat 32 (4 * savedRegs.length)).setWidth 64 = (saveRegion s).base := rfl
    simp only [below, e]
    exact Offset.contains_base _ (by simp only [savedRegs, List.length_cons, List.length_nil]; omega) (by omega)
  have entW : ∀ d < 16, d % 4 = 0 → u.mem.readW (addr ((pushed savedRegs s).gpr .esp) d) 32 =
      (pushed savedRegs s).mem.readW (addr ((pushed savedRegs s).gpr .esp) d) 32 := by
    intro d hd _
    rw [topAddr d (by omega)]
    exact frame.readW (r := saveRegion s) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => (hW r hr).1) (by decide)
  refine WP.mono (restore_ok (freed F u) read) ?_
  rintro t ⟨edi, esi, ebp, spT, eaxT, memT, -, -⟩
  have words : ∀ i < 4, t.mem.readW (addr (t.gpr .esp) (4 * i)) 32 =
      s.gpr (savedRegs[3 - i]'(by simp only [savedRegs, List.length_cons, List.length_nil]; omega)) := by
    intro i hi
    rw [memT, freed_mem, spT, spF, entW (4 * i) (by omega) (by omega)]
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
    rw [frame.readW (r := retRegion s) (Region.contains_self _ _) (fun r hr => (hW r hr).2) (by decide)]
    rw [entered_mem]
    refine (pushed_frame pushRegs_noSp (by simpa [savedRegs] using h16)).readW
      (r := ⟨(s.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro q hq
    simp only [List.mem_singleton] at hq; subst hq
    simp only [below, savedRegs, List.length_cons, List.length_nil]
    rw [Taint.sub_setWidth (by omega)]
    exact Offset.base_disjoint_below _ (n := 16) (k := 4) (by omega)
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
