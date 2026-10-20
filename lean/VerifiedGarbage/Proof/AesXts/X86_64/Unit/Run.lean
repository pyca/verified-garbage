module
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Spill

import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Pre
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesXts.Alpha16
import VerifiedGarbage.Proof.AesXts.Batch
import VerifiedGarbage.Proof.AesXts.X86_64.Steps

/-!
# XTS-AES of data units on x86-64: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps its arguments in `rbx`, `rbp`,
`r12`, `r13` and `r15`, its caller's callee-saved registers in their slots,
and changes memory only in the data, the scratch buffer and the stack below
(`Inv.step`, for any code whose frame is in those). `tweak_wp`: the prologue
and the call enciphering the tweak value leave `T = AES-enc(Key2, i)` in the
tweak (`TwPost`). `fin_wp`: the epilogue restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak. -/
abbrev Tp : Addr := S s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := S s₀ + BitVec.ofNat 64 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1))) (bytesAt s₀.mem (I s₀) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher := ciphOf enc (R s₀) (bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)))

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = W s₀
  rbp : s.gpr .rbp = s₀.gpr .rdx
  r12 : s.gpr .r12 = D s₀
  r13 : s.gpr .r13 = s₀.gpr .r9
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀, stk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (S s₀) s₀.gpr saved

theorem saved_bound : ∀ p ∈ saved, 2208 ≤ p.2 ∧ p.2 + 8 ≤ 2256 := by decide

/-- The registers `Inv` pins. -/
abbrev pinned : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

theorem pinned_cs : ∀ r ∈ pinned, r ∈ calleeSaved := by decide

theorem pinned_ne {r : Reg} (h : r ∈ pinned) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 ∧ r ≠ .r9 := by
  simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rsi_ofNat (s₀ : State) : BitVec.ofNat 64 (R s₀) = s₀.gpr .rdx := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The save, then `rest`, from the state it leaves. -/
theorem save_wp (s : State) {rest : List Instr} {Q : State → Prop}
    (hw : ∀ p ∈ saved, InRegions s.wr (Spill.slot (s.gpr .rax) p.2) 8)
    (h : ∀ s' : State, s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = Spill.saveMem s.mem (s.gpr .rax) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  rw [save_eq]
  exact Spill.save_then .rax saved hw (h _ rfl rfl rfl rfl)

theorem cS (s₀ : State) (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (S s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by omega)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the registers and writes only within
`rs`, each in the data, the first 2208 bytes of the scratch buffer or the
stack. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨S s₀, 2208⟩ ∨ r = stk s₀)
    (hf : Frame rs s.mem s'.mem)
    (hg : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], s'.gpr r = s.gpr r)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  rbx := by rw [hg _ (by simp), h.rbx]
  rbp := by rw [hg _ (by simp), h.rbp]
  r12 := by rw [hg _ (by simp), h.r12]
  r13 := by rw [hg _ (by simp), h.r13]
  r15 := by rw [hg _ (by simp), h.r15]
  rsp := by rw [hg _ (by simp), h.rsp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h | rfl
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩
    · exact ⟨stk s₀, by simp, fun _ h => h⟩)
  saved := h.saved.frame hf fun p hp' r hr =>
    (hp.slots_disj (hrs r hr)).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : Addr} {N Rr : Nat}
    (hT : Region.Sub ⟨T, 16⟩ ⟨S s₀, 2208⟩)
    (hD : Region.Sub ⟨Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨Dd, 16 * N⟩ ⟨S s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨T, 16⟩, ⟨Dd, 16 * N⟩, ⟨S s₀, 2176⟩, stk s]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact hD.elim .inl fun h => .inr (.inl h)
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (by rw [stk, stk, h.rsp])))
    hc.frame (fun r hr => hc.saved r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zp s₀) (Tp s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (I s₀) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem ldS_wp : WP isa (.block ldS) s₀ fun s => s = s₀.setReg .rax (S s₀) :=
  WP.of_runBlock ⟨_, ldS_ok s₀ (by
    rw [hp.rd]; exact in_rw (r := argR s₀) (by simp) (Region.contains_self _ _)), rfl⟩

theorem pro_wp : WP isa (.block pro) (s₀.setReg .rax (S s₀)) (ProPost s₀) := by
  have g₁ : ∀ r, r ≠ .rax → (s₀.setReg .rax (S s₀)).gpr r = s₀.gpr r := fun r h => gpr_setReg_of_ne _ _ h
  rw [pro, List.append_assoc]
  refine save_wp _ (fun p hp' => ?_) fun s₂ gpr₂ rd₂ wr₂ mem₂ => ?_
  · have := saved_bound p hp'
    rw [wr_setReg, hp.wr, gpr_setReg_self]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega))
  rw [WP.block_append_iff]
  obtain ⟨s₃, run₃, r15₃, rbx₃, rbp₃, r12₃, r13₃, g₃, mem₃', rd₃', wr₃'⟩ := setup_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [gpr₂, gpr_setReg_self] at r15₃
  rw [gpr₂] at rbx₃ rbp₃ r12₃ r13₃
  have mem₃ : s₃.mem = Spill.saveMem s₀.mem (S s₀) (s₀.setReg .rax (S s₀)).gpr saved := by
    rw [mem₃', mem₂, mem_setReg, gpr_setReg_self]
  have rd₃ : s₃.rd = s₀.rd := by rw [rd₃', rd₂, rd_setReg]
  have wr₃ : s₃.wr = s₀.wr := by rw [wr₃', wr₂, wr_setReg]
  have rbx₃' : s₃.gpr .rbx = W s₀ := by rw [rbx₃]; exact g₁ _ (by decide)
  have rbp₃' : s₃.gpr .rbp = s₀.gpr .rdx := by rw [rbp₃]; exact g₁ _ (by decide)
  have r12₃' : s₃.gpr .r12 = D s₀ := by rw [r12₃]; exact g₁ _ (by decide)
  have r13₃' : s₃.gpr .r13 = s₀.gpr .r9 := by rw [r13₃]; exact g₁ _ (by decide)
  have k₃ : ∀ r, r ≠ .rax → r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s₃.gpr r = s₀.gpr r :=
    fun r h₀ h₁ h₂ h₃ h₄ h₅ => by rw [g₃ r h₁ h₂ h₃ h₄ h₅, gpr₂]; exact g₁ r h₀
  have rdwr₃ : s₃.rd ++ s₃.wr = [schR s₀, tschR s₀, iR s₀, argR s₀, dataR s₀, scrR s₀] := by
    rw [rd₃, wr₃, hp.rd, hp.wr]; rfl
  have wr₃'' : s₃.wr = [dataR s₀, scrR s₀] := by rw [wr₃]; exact hp.wr
  have cI0 : (iR s₀).Contains (I s₀) 8 := by
    simpa using Offset.contains_base (I s₀) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  rw [tweakIn, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₄, run₄, g₄, mem₄, rd₄, wr₄⟩ := AesCbc.X86_64.copy_ok s₃ (dst := .r15) (src := .rcx) (d := tO) (e := 0)
    (P := Tp s₀) (Q := I s₀) (by rw [r15₃]) (by rw [r15₃, ← Offset.add_add])
    (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp)
    (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) cI0)
    (by rw [rdwr₃]; exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ (by decide) (by decide)))
    (by rw [wr₃'']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₃'', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by decide) (by decide)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [WP.block_append_iff]
  have wr₄' : s₄.wr = [dataR s₀, scrR s₀] := by rw [wr₄, wr₃'']
  obtain ⟨s₅, run₅, g₅, mem₅, rd₅, wr₅⟩ := zeroZ_ok s₄ (Z := Zp s₀)
    (by rw [g₄ _ (by decide), r15₃]) (by rw [g₄ _ (by decide), r15₃, ← Offset.add_add])
    (by rw [wr₄']; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₄', Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, r9₆, cs₆, mem₆, rd₆, wr₆⟩ := tArgs_ok s₅
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- The registers.
  have k₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₃.gpr r := fun r h => by rw [g₅ r h, g₄ r h]
  have r15₅ : s₅.gpr .r15 = S s₀ := by rw [k₅ _ (by decide), r15₃]
  have cs (r : Reg) (hr : r ∈ calleeSaved) : s₆.gpr r = s₃.gpr r := by
    rw [cs₆ r hr, k₅ r (AesCbc.X86_64.calleeSaved_ne_rax hr)]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅, rd₄, rd₃]
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅, wr₄, wr₃]
  have rsp₆ : s₆.gpr .rsp = s₀.gpr .rsp := by
    rw [cs _ (by simp [calleeSaved]), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  -- The memory.
  have f₃ : Frame [scrR s₀] s₀.mem s₃.mem := by
    rw [mem₃]
    exact (Spill.saveMem_frame_base s₀.mem (S s₀) _ (L := 2256) saved (fun p hp' => (saved_bound p hp').2)
      (by decide)).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  have f₄ : Frame [⟨Tp s₀, 16⟩] s₃.mem s₄.mem := by rw [mem₄]; exact AesCbc.copyMem_frame _ _ _
  have f₅ : Frame [⟨Zp s₀, 16⟩] s₄.mem s₅.mem := by rw [mem₅]; exact zero2_frame _ _
  have frame : Frame [scrR s₀] s₀.mem s₆.mem := by
    rw [mem₆]
    refine f₃.trans ((f₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  have sv₃ : Spill.Saved s₃.mem (S s₀) s₀.gpr saved := by
    intro p hp'
    rw [mem₃, Spill.saveMem_saved _ _ _ _ (by decide) p hp']
    refine g₁ _ ?_
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have sdisj : ∀ (r : Region), Region.Sub r ⟨S s₀, 2208⟩ → ∀ p ∈ saved, ∀ r' ∈ [r],
      Region.Disjoint ⟨Spill.slot (S s₀) p.2, 8⟩ r' := fun r hr p hp' r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact (hp.slots_disj (.inr (.inl hr))).sub_left (slot_sub p.2 (saved_bound p hp').1 (saved_bound p hp').2)
  have sv₆ : Spill.Saved s₆.mem (S s₀) s₀.gpr saved := by
    rw [mem₆]; exact (sv₃.frame f₄ (sdisj _ t_sub)).frame f₅ (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by simp [calleeSaved]), rbx₃'], by rw [cs _ (by simp [calleeSaved]), rbp₃'],
    by rw [cs _ (by simp [calleeSaved]), r12₃'], by rw [cs _ (by simp [calleeSaved]), r13₃'],
    by rw [cs _ (by simp [calleeSaved]), r15₃], rsp₆, rd₆', wr₆',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₆⟩, ?_, frame, ?_, ?_⟩
  · refine xpre_tweak hp rd₆' wr₆' rsp₆ ?_ ?_ (by rw [rdx₆, r15₅]) (by rw [rcx₆, r15₅]) r8₆ (by rw [r9₆, r15₅])
    · rw [rdi₆, k₅ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [rsi₆, k₅ _ (by decide), rbp₃', rsi_ofNat]
  · rw [mem₆, mem₅, Proof.Cmac.bytesAt_frame (zero2_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₄,
      AesCbc.copyMem_bytes _ (hp.i_scr.symm.sub_left (scr_sub (by simp [tO]))),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₆, mem₅, zero2_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀, stk s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ r = stk s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (W s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (W s₀) (16 * (R s₀ + 1)) := by
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases hd r hr with rfl | rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 1) {s₂ : State} (h₂ : ProPost s₀ s₂) :
    WP isa (.call n c) s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true ok nosp depth h₂.pre) fun s₃ c => ?_
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  have eK : bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1)) = bytesAt s₀.mem (K s₀) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega)
  refine ⟨Inv.call hp h₂.inv z_sub (.inr t_sub) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stk s₀, by simp, by rw [stk, stk, h₂.inv.rsp]; exact fun _ h => h⟩
  · have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (K s₀) (16 * (R s₀ + 1))) c.out h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp {f : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
      ∃ t s', Exec isa f.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s')
    (nosp : NoSp f.code) (depth : f.code.depth ≤ 1) :
    WP isa (tweak f) s₀ (TwPost s₀) := by
  refine WP.seq (WP.mono (ldS_wp hp) fun s₁ h₁ => ?_)
  subst h₁
  exact WP.seq (WP.mono (pro_wp hp) fun s₂ h₂ => tcall_wp hp ok nosp depth h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (D s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨D s₀, 16 * N⟩, scrR s₀, stk s₀] s₀.mem s.mem

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨D s₀, 16 * N⟩, scrR s₀, stk s₀] s₀.mem m

omit hp in
theorem AllPost.mem {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) : AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)

theorem blocks_call (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (nosp : NoSp c) (depth : c.depth ≤ 1) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.call n c) s (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc ok nosp depth hpre) fun s' x => ?_
  have dS : Region.Sub ⟨D s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  have eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  have eD : Spec.Cbc.blocksAt s.mem (D s₀) N = Spec.Cbc.blocksAt s₀.mem (D s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_scr.sub_left dS
      · exact hp.stk_data.symm.sub_left dS) (by have := hp.data_wrap; omega)
  refine ⟨Inv.call hp h.inv t_sub (.inl dS) x, ?_, ?_, ?_⟩
  · rw [x.out, eW, h.t, eD]
  · rw [x.tw, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, fun _ h => h⟩
      · exact ⟨stk s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stk s₀, by simp, by rw [stk, stk, h.inv.rsp]; exact fun _ h => h⟩

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem := by
  rw [restore_eq]
  refine WP.mono (Spill.restore_ok .r15 saved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.r15]; exact h.saved)) fun s' ⟨g₁, g₂, mem', _⟩ =>
      ⟨⟨Spill.calleeSaved_ok g₁ g₂ (by decide) h.rsp, ?_⟩, mem'⟩
  · have := saved_bound p hp'
    rw [h.rd, h.wr, hp.rd, hp.wr, h.r15]
    exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by omega))
  · rw [mem']
    refine h.frame.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact Offset.base_disjoint_below _ (by decide)

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : Addr} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨Dd, 16 * N⟩) (hT : Region.Sub ⟨T, 16⟩ (scrR s₀))
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub
    · rw [stk, hrsp]; exact hp.stk_data.symm.sub_left hX) hn

end

end VG.Proof.AesXts.X86_64.Unit
