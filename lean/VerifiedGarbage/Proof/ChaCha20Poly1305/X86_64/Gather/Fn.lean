import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Callee
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: the function

Untrusted: everything here is checked by Lean. With `B` the base of the
1808 bytes of stack below the stack pointer (`rsp = B + 1808`),
`vg_chacha20_poly1305_seal_gather` pushes the six argument registers in its
frame at `B + 1760` (`pushed`), puts `src` in `r11` and `dst` in `rdi`
(`entered_wp`), gathers the slices to `dst` (`gathered_wp`, `gather_wp`),
loads the call's arguments from the frame and the stack arguments
(`ready_wp`), and calls `vg_chacha20_poly1305_seal` on them in place with
`tag` pushed at `B + 1752` (`called_wp`, by its shared contract); the call
keeps our frame and the return address above it.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm)
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width entry gather callArgs sealGather)
open VG.Proof.AesGcm.X86_64 (offset_nat)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20Poly1305 (encrypt gathered gatheredLen pMax)
open VG.Proof.ChaCha20Poly1305 (bytesAt_frame bytesAt_writeBytes_self)

/-- The argument registers our frame keeps. -/
abbrev saved : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-! ## The blocks -/

/-- `entry`: `src` into `r11`, and `dst` (`[rsp + 56]`) into `rdi`. -/
theorem entry_ok (a : State) {P : Addr} (hsp : a.gpr .rsp = P)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8) :
    WP isa (.block entry) a fun e => e.gpr .r11 = a.gpr .r8 ∧
      e.gpr .rdi = a.mem.readW (P + BitVec.ofNat 64 56) 64 ∧
      (∀ r, r ≠ .r11 → r ≠ .rdi → e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [entry, hsp, r₅₆], ?_⟩
  exact ⟨by simp [gpr_setReg], by simp [gpr_setReg], fun r h₁ h₂ => by simp [gpr_setReg, h₁, h₂], rfl, rfl, rfl⟩

/-- `callArgs`: the call's arguments, from the frame and our stack arguments. -/
theorem callArgs_ok (a : State) {P : Addr} (hsp : a.gpr .rsp = P)
    (r₁₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 16) 8)
    (r₂₄ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 24) 8)
    (r₃₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 32) 8)
    (r₄₀ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 40) 8)
    (r₅₆ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 56) 8)
    (r₆₄ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 64) 8)
    (r₇₂ : InRegions (a.rd ++ a.wr) (P + BitVec.ofNat 64 72) 8) :
    WP isa (.block callArgs) a fun e => e.gpr .rdi = a.mem.readW (P + BitVec.ofNat 64 40) 64 ∧
      e.gpr .rsi = a.mem.readW (P + BitVec.ofNat 64 32) 64 ∧
      e.gpr .rdx = a.mem.readW (P + BitVec.ofNat 64 24) 64 ∧
      e.gpr .rcx = a.mem.readW (P + BitVec.ofNat 64 16) 64 ∧
      e.gpr .r8 = a.mem.readW (P + BitVec.ofNat 64 56) 64 ∧
      e.gpr .r9 = a.mem.readW (P + BitVec.ofNat 64 64) 64 ∧
      e.gpr .rax = a.mem.readW (P + BitVec.ofNat 64 72) 64 ∧
      (∀ r ∈ calleeSaved, e.gpr r = a.gpr r) ∧ e.mem = a.mem ∧ e.rd = a.rd ∧ e.wr = a.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [callArgs, hsp, r₁₆, r₂₄, r₃₂, r₄₀, r₅₆, r₆₄, r₇₂], ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]

/-! ## The layout -/

section
variable (s : State)

/-- The base of the 1808 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.gpr .rsp - BitVec.ofNat 64 1808

/-- Our frame. -/
abbrev FR : Region := ⟨Bs s + BitVec.ofNat 64 1760, 48⟩

/-- The memory after the push of our frame. -/
abbrev eM : Mem := (pushed saved s).mem

/-- The memory once the slices are gathered at `dst`. -/
abbrev gM : Mem := writeBytes (eM s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_chacha20_poly1305_seal` reads (with `tag`
pushed for it) and writes. -/
abbrev rdC : List Region := [kR s, nR s, aR s, ⟨Bs s + BitVec.ofNat 64 1752, 8⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

theorem add_ofNat_sub_ofNat (B : Addr) {a b : Nat} (h : b ≤ a) :
    B + BitVec.ofNat 64 a - BitVec.ofNat 64 b = B + BitVec.ofNat 64 (a - b) := by
  rw [← Offset.ofNat_sub_ofNat h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.gpr .rsp = Bs s + BitVec.ofNat 64 1808
  hBn : (Bs s).toNat + 1840 ≤ 2 ^ 64
  hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 1808

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  have w₁ : 1808 ≤ (s.gpr .rsp).toNat := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have w₂ : (s.gpr .rsp).toNat + 32 ≤ 2 ^ 64 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBv : (Bs s).toNat = (s.gpr .rsp).toNat - 1808 := toNat_sub_ofNat w₁
  exact ⟨hs, (BitVec.sub_add_cancel _ _).symm, by omega, hBv⟩

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 1808) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub (stkR s) :=
  Offset.sub_base _ h'

theorem covers_of_mem' {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem hP (s : State) : (pushed saved s).gpr .rsp = Bs s + BitVec.ofNat 64 1760 := by
  rw [pushed_rsp, Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1808 by decide)]; rfl

theorem hPwr (s : State) : (pushed saved s).wr = FR s :: s.wr := by
  rw [pushed_wr, Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1808 by decide)]; rfl

theorem fr_sub (s : State) : (FR s).Sub (stkR s) := stk_sub s 1760 48 (by decide)

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem w₁ : 1808 ≤ (s.gpr .rsp).toNat := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The stack arguments. -/
theorem argAddr (i : Nat) : stackArgAddr s i = Bs s + BitVec.ofNat 64 (1816 + 8 * i) := by
  show s.gpr .rsp + BitVec.ofNat 64 (8 * (i + 1)) = _
  rw [h.hB, Offset.add_ofNat_add_ofNat]; congr 2; omega

theorem hargR : argR s = ⟨Bs s + BitVec.ofNat 64 1816, 24⟩ := by
  show (⟨stackArgAddr s 0, 24⟩ : Region) = _
  rw [h.argAddr]

theorem pushes : Frame [FR s] s.mem (eM s) ∧
    ∀ j (hj : j < saved.length), (eM s).readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 = s.gpr saved[j] := by
  have := pushRegs_mem s saved (by decide) (by have := h.w₁; simp only [List.length_cons, List.length_nil]; omega)
  rw [Offset.sub_ofNat_eq _ (show 8 * saved.length ≤ 1808 by decide)] at this
  exact this

theorem frame_eM : Frame [FR s] s.mem (eM s) := h.pushes.1

/-- The words of our frame: the argument registers. -/
theorem pushedW (j : Nat) (hj : j < 6) (d : Nat) (hd : d + 8 * (j + 1) = 1808) :
    (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 = s.gpr (saved[j]'hj) := by
  have := h.pushes.2 j hj
  rw [Offset.sub_ofNat_eq _ (show 8 * (j + 1) ≤ 1808 by omega), show 1808 - 8 * (j + 1) = d by omega] at this
  exact this

/-- The memory the push left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint (stkR s)) {x : Addr} (hx : r.Contains x 1) : eM s x = s.mem x :=
  h.frame_eM x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (fr_sub s x hc)

/-- The descriptors and the slices, after the push. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eM s x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bds, bls, -⟩ := h.pre
  intro r hr x hx
  refine (h.keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact bds.symm
  · exact (bls r hr).symm

theorem hpt : Spec.Gcm.gathered 64 (eM s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s :=
  (Proof.Gcm.length_gathered _ _ _ _).trans h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem frame_gM : Frame [dR s] (eM s) (gM s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- A word of the stack, once the slices are gathered. -/
theorem gFrame (d : Nat) (hd : d + 8 ≤ 1808) :
    (gM s).readW (Bs s + BitVec.ofNat 64 d) 64 = (eM s).readW (Bs s + BitVec.ofNat 64 d) 64 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, bd, -⟩ := h.pre
  refine Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact bd.sub_left (stk_sub s d 8 hd)

/-- A stack argument, once the slices are gathered. -/
theorem gArg (i : Nat) (hi : i < 3) :
    (gM s).readW (Bs s + BitVec.ofNat 64 (1816 + 8 * i)) 64 = stackArg s i := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, darg, -⟩ := h.pre
  have hBn := h.hBn
  have hs : Region.Sub ⟨Bs s + BitVec.ofNat 64 (1816 + 8 * i), 8⟩ (argR s) := by
    rw [h.hargR]; exact Offset.sub _ (by omega) (by omega)
  rw [Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact darg.symm.sub_left hs) (by decide)]
  rw [Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)]
  rw [← h.argAddr]; rfl

end Lay

/-! ## The phases -/

/-- After the push and the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eM s
  r11 : e.gpr .r11 = Src s
  rdi : e.gpr .rdi = Dst s
  gpr : ∀ r, r ≠ .r11 → r ≠ .rdi → r ≠ .rsp → e.gpr r = s.gpr r
  rsp : e.gpr .rsp = Bs s + BitVec.ofNat 64 1760
  rd : e.rd = s.rd
  wr : e.wr = FR s :: s.wr
  mx : e.mxcsr = s.mxcsr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entry) (pushed saved s) (Entered s) := by
  have hBn := h.hBn
  have r₅₆ : InRegions ((pushed saved s).rd ++ (pushed saved s).wr)
      (Bs s + BitVec.ofNat 64 1760 + BitVec.ofNat 64 56) 8 := by
    rw [pushed_rd, Offset.add_ofNat_add_ofNat]
    refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.1]; simp), ?_⟩
    rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)
  refine WP.mono_mx (by decide +kernel) (entry_ok (pushed saved s) (hP s) r₅₆)
    fun e ⟨r11e, rdie, ge, me, rde, wre⟩ mxe => ?_
  refine ⟨me, by rw [r11e, pushed_gpr _ _ (by decide)], ?_, fun r h₁ h₂ h₃ => ?_, ?_, by rw [rde, pushed_rd],
    by rw [wre, hPwr s], by rw [mxe, pushed_mxcsr]⟩
  · rw [rdie, Offset.add_ofNat_add_ofNat, Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)]
    show _ = s.mem.readW (stackArgAddr s 0) 64
    rw [h.argAddr]
  · rw [ge r h₁ h₂, pushed_gpr _ _ h₃]
  · rw [ge _ (by decide) (by decide), hP s]

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, -, -, -, -, -, -, -, dds, dls, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ods, -, -, -, hgl,
    hpm⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  have hpm' : L s ≤ 64 * (2 ^ 32 - 1) := hpm
  exact { r11 := he.r11
          r9 := by rw [he.gpr _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rdi := he.rdi
          hcnt := (s.gpr .r9).isLt
          dw := ods
          lt := by omega
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_of_mem' (List.mem_append_left _ (by rw [he.rd, rd]; simp))
          lsr := fun r hr => covers_of_mem' (List.mem_append_left _ (by
            rw [hls] at hr; rw [he.rd, rd]; simp [hr]))
          dw' := covers_of_mem' (by rw [he.wr, wr]; simp)
          dsd := dds.symm
          lsd := fun r hr => (dls r (by rw [hls] at hr; exact hr)).symm }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gM s
  gpr : ∀ r, r ∉ gatherRegs → r ≠ .rsp → g.gpr r = s.gpr r
  rsp : g.gpr .rsp = Bs s + BitVec.ofNat 64 1760
  rd : g.rd = s.rd
  wr : g.wr = FR s :: s.wr
  mx : g.mxcsr = s.mxcsr

theorem gathered_wp (w : Width) {s e : State} (h : Lay s) (he : Entered s e) : WP isa (gather w) e (Gathered s) := by
  refine WP.mono_mx (by cases w <;> decide +kernel) (gather_wp w e (gatherPre_of h he)) fun g ⟨mg, kg⟩ mxg => ?_
  rw [he.mem, h.hpt] at mg
  exact ⟨mg, fun r hr hsp => (kg.gpr r hr).trans (he.gpr r (fun e => hr (by simp [e]))
      (fun e => hr (by simp [e])) hsp),
    (kg.gpr _ (by decide)).trans he.rsp, kg.rd.trans he.rd, kg.wr.trans he.wr, mxg.trans he.mx⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gM s
  rdi : c.gpr .rdi = K s
  rsi : c.gpr .rsi = Nn s
  rdx : c.gpr .rdx = Ad s
  rcx : c.gpr .rcx = s.gpr .rcx
  r8 : c.gpr .r8 = Dst s
  r9 : c.gpr .r9 = stackArg s 1
  rax : c.gpr .rax = Tg s
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → c.gpr r = s.gpr r
  rsp : c.gpr .rsp = Bs s + BitVec.ofNat 64 1760
  rd : c.rd = s.rd
  wr : c.wr = FR s :: s.wr
  mx : c.mxcsr = s.mxcsr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgs) g (Ready s) := by
  have hBn := h.hBn
  have inFr (d : Nat) (hd : d + 8 ≤ 48) :
      InRegions (g.rd ++ g.wr) (Bs s + BitVec.ofNat 64 1760 + BitVec.ofNat 64 d) 8 := by
    rw [hg.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨FR s, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains _ (by omega) (by omega) (by omega)⟩
  have inArg (d : Nat) (h₁ : 56 ≤ d) (hd : d + 8 ≤ 80) :
      InRegions (g.rd ++ g.wr) (Bs s + BitVec.ofNat 64 1760 + BitVec.ofNat 64 d) 8 := by
    rw [hg.rd, Offset.add_ofNat_add_ofNat]
    refine ⟨argR s, List.mem_append_left _ (by rw [h.pre.1]; simp), ?_⟩
    rw [h.hargR]; exact Offset.contains _ (by omega) (by omega) (by omega)
  refine WP.mono_mx (by decide +kernel) (callArgs_ok g hg.rsp (inFr 16 (by decide)) (inFr 24 (by decide))
      (inFr 32 (by decide)) (inFr 40 (by decide)) (inArg 56 (by decide) (by decide))
      (inArg 64 (by decide) (by decide)) (inArg 72 (by decide) (by decide)))
    fun c ⟨rdic, rsic, rdxc, rcxc, r8c, r9c, raxc, csc, mc, rdc, wrc⟩ mxc => ?_
  simp only [Offset.add_ofNat_add_ofNat, Nat.reduceAdd, hg.mem] at rdic rsic rdxc rcxc r8c r9c raxc
  have g56 := h.gArg 0 (by decide)
  have g64 := h.gArg 1 (by decide)
  have g72 := h.gArg 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at g56 g64 g72
  refine ⟨mc.trans hg.mem, ?_, ?_, ?_, ?_, r8c.trans g56, r9c.trans g64, raxc.trans g72, fun r hr hsp => ?_,
    (csc _ (by decide)).trans hg.rsp, rdc.trans hg.rd, wrc.trans hg.wr, mxc.trans hg.mx⟩
  · rw [rdic, h.gFrame 1800 (by decide)]; exact h.pushedW 0 (by decide) 1800 rfl
  · rw [rsic, h.gFrame 1792 (by decide)]; exact h.pushedW 1 (by decide) 1792 rfl
  · rw [rdxc, h.gFrame 1784 (by decide)]; exact h.pushedW 2 (by decide) 1784 rfl
  · rw [rcxc, h.gFrame 1776 (by decide)]; exact h.pushedW 3 (by decide) 1776 rfl
  · rw [csc r hr]
    refine hg.gpr r (fun hm => ?_) hsp
    simp only [calleeSaved, gatherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr hm
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hm

/-! ## The call -/

section
variable (c : State)

/-- The state the body of the call's frame starts in: `tag` pushed. -/
abbrev qS : State := pushed [.rax] c

end

/-- The state the callee starts in, given the regions it reads and writes. -/
abbrev xS (s c : State) : State := (qS c).callEntry.withRegions (rdC s) (wrC s)

theorem xgpr_eq {s c : State} {r : Reg} (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr _ _ hr]

section
variable {s c : State} (h : Lay s) (hc : Ready s c)
include h hc

omit h in
theorem Ready.qsp : (qS c).gpr .rsp = Bs s + BitVec.ofNat 64 1752 := by
  rw [pushed_rsp, hc.rsp, show 8 * [Reg.rax].length = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)]

omit h in
theorem Ready.qwr : (qS c).wr = ⟨Bs s + BitVec.ofNat 64 1752, 8⟩ :: FR s :: s.wr := by
  rw [pushed_wr, hc.rsp, hc.wr, show 8 * [Reg.rax].length = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)]

omit h in
theorem Ready.qrd : (qS c).rd = s.rd := by rw [pushed_rd, hc.rd]

theorem Ready.hn : 8 * [Reg.rax].length ≤ (c.gpr .rsp).toNat := by
  have := h.hBn
  rw [hc.rsp, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 1760) (by decide),
    Nat.mod_eq_of_lt (by omega)]
  simp only [List.length_cons, List.length_nil]; omega

/-- The push of `tag`. -/
theorem Ready.qmem : Frame [⟨Bs s + BitVec.ofNat 64 1752, 8⟩] c.mem (qS c).mem ∧
    (qS c).mem.readW (Bs s + BitVec.ofNat 64 1752) 64 = Tg s := by
  have := pushRegs_mem c [.rax] (by decide) (hc.hn h)
  have h₁ := this.1
  have h₂ := this.2 0 (by decide)
  rw [hc.rsp, show 8 * [Reg.rax].length = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₁
  rw [hc.rsp, show 8 * (0 + 1) = 8 from rfl, add_ofNat_sub_ofNat _ (by decide)] at h₂
  exact ⟨h₁, h₂.trans hc.rax⟩

omit h in
theorem Ready.xsp : (xS s c).gpr .rsp = Bs s + BitVec.ofNat 64 1744 := by
  rw [State.withRegions_gpr, State.callEntry_rsp, hc.qsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]


omit h in
/-- The return address of the call. -/
theorem Ready.xmem : Frame [⟨Bs s + BitVec.ofNat 64 1744, 8⟩] (qS c).mem (xS s c).mem := by
  rw [State.withRegions_mem, State.callEntry_mem, hc.qsp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
    add_ofNat_sub_ofNat _ (by decide)]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

omit h in
theorem Ready.xarg : stackArgAddr (xS s c) 0 = Bs s + BitVec.ofNat 64 1752 := by
  show (xS s c).gpr .rsp + BitVec.ofNat 64 (8 * (0 + 1)) = _
  rw [hc.xsp, Offset.add_ofNat_add_ofNat]

theorem Ready.xtag : stackArg (xS s c) 0 = Tg s := by
  have hBn := h.hBn
  show (xS s c).mem.readW (stackArgAddr (xS s c) 0) 64 = _
  rw [hc.xarg, Frame.readW (hc.xmem) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)]
  exact (hc.qmem h).2

/-- What the call needs. -/
theorem Ready.call : callPre (xS s c) ∧ Covers (rdC s ++ wrC s) ((qS c).rd ++ (qS c).wr) ∧
    Covers (wrC s) (qS c).wr := by
  obtain ⟨rd, wr, kd, kt, nd, nt, ad, at_, dt, -, -, -, -, -, bk, bn, ba, bd, bt, -, -, ok, on, oa, od, ot,
    -⟩ := h.pre
  have hBn := h.hBn
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := xgpr_eq hr
  have hstk : below (Bs s + BitVec.ofNat 64 1744) 1744 = ⟨Bs s, 1744⟩ := by
    simp only [below, add_ofNat_sub_ofNat _ (show 1744 ≤ 1744 by decide), Nat.sub_self, BitVec.add_zero]
  have hxsp : (Bs s + BitVec.ofNat 64 1744).toNat = (Bs s).toNat + 1744 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 1744) (by decide),
      Nat.mod_eq_of_lt (by omega)]
  have sb (d n : Nat) (hd : d + n ≤ 1808) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := hr.sub_left (stk_sub s d n hd)
  have s0 (n : Nat) (hd : n ≤ 1808) {r : Region} (hr : (stkR s).Disjoint r) :
      (⟨Bs s, n⟩ : Region).Disjoint r := hr.sub_left (Region.sub_prefix hd)
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, hx .rdi (by decide), hx .rsi (by decide),
      hx .rdx (by decide), hx .rcx (by decide), hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx,
      hc.rcx, hc.r8, hc.r9, hc.xtag h, hc.xarg, hc.xsp, hstk]
    exact ⟨by omega, by omega, trivial, trivial, kd, kt, nd, nt, ad, at_, dt, (sb 1752 8 (by decide) bd).symm,
      (sb 1752 8 (by decide) bt).symm, sb 1744 8 (by decide) bk, sb 1744 8 (by decide) bn,
      sb 1744 8 (by decide) ba, sb 1744 8 (by decide) bd, sb 1744 8 (by decide) bt,
      Offset.disjoint _ (.inl (by omega)) (by omega) (by omega), s0 1744 (by decide) bk, s0 1744 (by decide) bn,
      s0 1744 (by decide) ba, s0 1744 (by decide) bd, s0 1744 (by decide) bt,
      Offset.base_disjoint _ (by decide) (by omega), ok, on, oa, od, ot⟩
  · rw [hc.qrd, hc.qwr, rd, wr]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩
  · rw [hc.qwr, wr]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, hcn⟩
    · exact ⟨_, by simp, hcn⟩

end

/-- After the call, and the pop of `tag`. -/
structure Called (s z : State) : Prop where
  out : gatherPost s z
  ret : z.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → z.gpr r = s.gpr r
  rsp : z.gpr .rsp = Bs s + BitVec.ofNat 64 1760
  rd : z.rd = s.rd
  wr : z.wr = FR s :: s.wr
  mx : z.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem called_wp (F : SealFn) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1)) c (Called s) := by
  obtain ⟨-, -, kd, -, nd, -, ad, -, -, -, -, -, rdd, rt, bk, bn, ba, bd, -, -, -, ok, on, oa, od, -⟩ := h.pre
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  have hBn := h.hBn
  have hdep := F.depth
  have hx (r : Reg) (hr : r ≠ .rsp) : (xS s c).gpr r = c.gpr r := xgpr_eq hr
  refine WP.frame (by simp) (by decide) (by decide) (hc.hn h) (WP.call_sp_mx F.verified.1 F.sp (by omega)
    (sealSpec_pre hcp) hcov hw fun s' rd' wr' cs' fr' _ ⟨s₂, m₂, _, post'⟩ mx' => ?_)
  have rsp' : s'.gpr .rsp = (qS c).gpr .rsp := cs' .rsp (by decide)
  refine ⟨rsp', wr', ?_⟩
  have hpost := sealSpec_post post'
  simp only [hx .rdi (by decide), hx .rsi (by decide), hx .rdx (by decide), hx .rcx (by decide),
    hx .r8 (by decide), hx .r9 (by decide), hc.rdi, hc.rsi, hc.rdx, hc.rcx, hc.r8, hc.r9, hc.xtag h, m₂] at hpost
  -- The callee's memory on entry: ours, with `tag` and its return address pushed below our frame.
  have fx : Frame [⟨Bs s + BitVec.ofNat 64 1752, 8⟩, ⟨Bs s + BitVec.ofNat 64 1744, 8⟩] (gM s) (xS s c).mem := by
    rw [← hc.mem]
    exact ((hc.qmem h).1.mono (fun r hr => by simp at hr ⊢; exact Or.inl hr)).trans
      ((hc.xmem).mono (fun r hr => by simp at hr ⊢; exact Or.inr hr))
  have apart {r : Region} (hr : (stkR s).Disjoint r) :
      ∀ r' ∈ [(⟨Bs s + BitVec.ofNat 64 1752, 8⟩ : Region), ⟨Bs s + BitVec.ofNat 64 1744, 8⟩], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact (hr.sub_left (stk_sub s 1752 8 (by decide))).symm
    · exact (hr.sub_left (stk_sub s 1744 8 (by decide))).symm
  rw [bytesAt_frame fx (apart bk) (by omega), bytesAt_frame fx (apart bn) (by omega),
    bytesAt_frame fx (apart ba) (by omega), bytesAt_frame fx (apart bd) (by omega)] at hpost
  -- The key, the nonce and the additional data are what they were; the data is the slices gathered.
  have hfc : Frame [FR s, dR s] s.mem (gM s) :=
    (h.frame_eM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
      (h.frame_gM.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))
  have apart' {r : Region} (h₁ : (stkR s).Disjoint r) (h₂ : r.Disjoint (dR s)) :
      ∀ r' ∈ [FR s, dR s], r.Disjoint r' := by
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact h₁.symm.sub_right (fr_sub s)
    · exact h₂
  rw [bytesAt_frame hfc (apart' bk kd) (by omega), bytesAt_frame hfc (apart' bn nd) (by omega),
    bytesAt_frame hfc (apart' ba ad) (by omega)] at hpost
  have hd : bytesAt (gM s) (Dst s) (L s) = pt s (Cnt s) := by
    rw [← h.hlen]
    exact bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (stackArg s 1).isLt)
  rw [hd] at hpost
  refine ⟨by simp only [gatherPost, popped_mem]; exact hpost, ?_, fun r hr hsp => ?_, ?_, ?_, ?_, ?_⟩
  · -- The return address: neither the push, nor the copy, nor the call wrote it.
    have hsp' : (qS c).gpr .rsp = Bs s + BitVec.ofNat 64 1752 := hc.qsp
    have hbelow : below ((qS c).gpr .rsp) (F.code.x86_64Depth + 8) =
        ⟨Bs s + BitVec.ofNat 64 (1744 - F.code.x86_64Depth), F.code.x86_64Depth + 8⟩ := by
      rw [hsp']; simp only [below]
      rw [add_ofNat_sub_ofNat _ (by omega), show 1752 - (F.code.x86_64Depth + 8) = 1744 - F.code.x86_64Depth by omega]
    have e : s.gpr .rsp = Bs s + BitVec.ofNat 64 1808 := h.hB
    rw [popped_mem, e]
    have r₁ : s'.mem.readW (Bs s + BitVec.ofNat 64 1808) 64 = (qS c).mem.readW (Bs s + BitVec.ofNat 64 1808) 64 := by
      refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, hbelow] at hr
      rcases hr with (rfl | rfl) | rfl
      · rw [← e]; exact rdd
      · rw [← e]; exact rt
      · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    have r₂ : (qS c).mem.readW (Bs s + BitVec.ofNat 64 1808) 64 = c.mem.readW (Bs s + BitVec.ofNat 64 1808) 64 :=
      Frame.readW (hc.qmem h).1 (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)
    have r₃ : (gM s).readW (Bs s + BitVec.ofNat 64 1808) 64 = (eM s).readW (Bs s + BitVec.ofNat 64 1808) 64 :=
      Frame.readW h.frame_gM (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← e]; exact rdd) (by decide)
    have r₄ : (eM s).readW (Bs s + BitVec.ofNat 64 1808) 64 = s.mem.readW (Bs s + BitVec.ofNat 64 1808) 64 :=
      Frame.readW h.frame_eM (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (by decide)
    rw [r₁, r₂, hc.mem, r₃, r₄]
  · have hra : r ≠ .rax := fun e => by subst e; simp [calleeSaved] at hr
    rw [popped_gpr _ _ _ hsp hra, cs' r hr, pushed_gpr _ _ hsp, hc.cs r hr hsp]
  · rw [popped_rsp, rsp', hc.qsp, Offset.add_ofNat_add_ofNat]; rfl
  · rw [popped_rd, rd', hc.qrd]
  · rw [popped_wr, wr', hc.qwr]; rfl
  · rw [popped_mxcsr, mx', pushed_mxcsr, hc.mx]

/-- The body of our frame. -/
theorem frameBody_wp (w : Width) (F : SealFn) {s : State} (h : Lay s) :
    WP isa (.seq (.block entry) (.seq (gather w) (.seq (.block callArgs)
      (.frame (.push [.rax]) (.call F.name F.code) (.pop .rax 1))))) (pushed saved s) (Called s) := by
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp w h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  exact called_wp F h hc

theorem sealGather_wp (w : Width) (F : SealFn) {s : State} (hs : gatherPre s) :
    WP isa (sealGather w F.name F.code) s fun z => abiPreserved s z ∧ gatherPost s z := by
  have h := lay hs
  have hn : 8 * saved.length ≤ (s.gpr .rsp).toNat := by have := h.w₁; simp only [List.length_cons, List.length_nil]; omega
  refine WP.frame (by simp) (by decide) (by decide) hn (WP.mono (frameBody_wp w F h) fun z hz => ?_)
  refine ⟨by rw [hz.rsp, hP s], by rw [hz.wr, hPwr s], ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · by_cases hsp : r = .rsp
    · subst hsp
      rw [popped_rsp, hz.rsp, Offset.add_ofNat_add_ofNat, h.hB]; rfl
    · have hra : r ≠ .rax := fun e => by subst e; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ hsp hra, hz.cs r hr hsp]
  · rw [popped_mem]; exact hz.ret
  · rw [popped_mxcsr]; exact hz.mx
  · have := hz.out
    simp only [gatherPost, popped_mem] at this ⊢
    exact this

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
