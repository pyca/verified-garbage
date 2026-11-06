module

public import VerifiedGarbage.Impl.Xdh.X86
public import VerifiedGarbage.Proof.Xdh.Common
public import VerifiedGarbage.Proof.Xdh.Rel
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Reduce
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.Xdh.X86
meta import VerifiedGarbage.Proof.Xdh.Common
meta import VerifiedGarbage.Proof.Xdh.Rel
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.X86.Inline
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# X25519 and X448 exchange, with RFC 7748's check, on x86

Untrusted: everything here is checked by Lean. As on RISC-V
(`Proof/Xdh/RISCV64.lean`): for any callee `c` that never writes `esp`, whose
calls and frames use at most `cs` bytes below its stack pointer, and whose
contract `k` its proof gives (`Callee`), `Impl.Xdh.X86.exchange` allocates
16 bytes at `E - 16` (`E` the stack pointer on entry), copies our four
arguments there (`copied_wp`), calls `c` (`called_wp`), which sees them as
its own and writes neither them nor ours, frees the frame, loads `out` from
our arguments (`restored_wp`), ORs the `n` bytes there into `ecx`
(`orBytes_wp`) and returns the result in `eax` (`checked_wp`). Its calls and
frames use `20 + cs` bytes below `E`: the frame, the return address and the
callee's. Two runs whose arguments agree (`Pub`) leak the same trace
(`exchange_ct`).
-/

@[expose] public section

namespace VG.Proof.Xdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Xdh.X86
open VG.Spec.X25519 (bytesAt)
open VG.Proof.Xdh (Eq2 TT rel_seq ct_of)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movzx8 {d b : Reg} {o : Nat} {a : Addr} (ha : addr (s.gpr b) o = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q := by
  refine cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [reduceExec, State.load8, ea_mk, ha, hin]

theorem wp_xori {d : Reg} {v : BitVec 32} (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

end

section
variable (n w : Nat) (s : State)

/-- The regions of the arguments, of our arguments themselves, of the return
address and of the `S` bytes below it. -/
abbrev outR : Region := ⟨(arg s 0).setWidth 64, n⟩
abbrev scR : Region := ⟨(arg s 1).setWidth 64, n⟩
abbrev ptR : Region := ⟨(arg s 2).setWidth 64, n⟩
abbrev wsR : Region := ⟨(arg s 3).setWidth 64, w⟩
abbrev argR : Region := ⟨argAddr s 0, 16⟩
abbrev retR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stkR (S : Nat) : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 S, S⟩

end

/-- What a function with the signature of `vg_x25519` (`n`-byte buffers, `w`
bytes of working space), whose calls and frames use `S` bytes of stack,
needs at its entry. -/
def Pre (n w S : Nat) (s : State) : Prop :=
  s.rd = [scR n s, ptR n s, argR s] ∧ s.wr = [outR n s, wsR w s] ∧
    (outR n s).Disjoint (scR n s) ∧ (outR n s).Disjoint (ptR n s) ∧ (outR n s).Disjoint (wsR w s) ∧
    (outR n s).Disjoint (argR s) ∧ (scR n s).Disjoint (wsR w s) ∧ (ptR n s).Disjoint (wsR w s) ∧
    (wsR w s).Disjoint (argR s) ∧
    (retR s).Disjoint (outR n s) ∧ (retR s).Disjoint (scR n s) ∧ (retR s).Disjoint (ptR n s) ∧
    (retR s).Disjoint (wsR w s) ∧ (retR s).Disjoint (argR s) ∧
    (stkR s S).Disjoint (outR n s) ∧ (stkR s S).Disjoint (scR n s) ∧ (stkR s S).Disjoint (ptR n s) ∧
    (stkR s S).Disjoint (wsR w s) ∧ (stkR s S).Disjoint (argR s) ∧
    (arg s 0).toNat + n ≤ 2 ^ 32 ∧ (arg s 1).toNat + n ≤ 2 ^ 32 ∧ (arg s 2).toNat + n ≤ 2 ^ 32 ∧
    (arg s 3).toNat + w ≤ 2 ^ 32 ∧ S ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

/-- What it leaves: `f` of the scalar and the point at `out`, and 0 in `eax`
(the low word of the result in `edx:eax`) if that is all zero, 1 otherwise. -/
def ExPost (n : Nat) (f : List Byte → List Byte → List Byte) (s s' : State) : Prop :=
  bytesAt s'.mem ((arg s 0).setWidth 64) n =
      f (bytesAt s.mem ((arg s 1).setWidth 64) n) (bytesAt s.mem ((arg s 2).setWidth 64) n) ∧
    (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 =
      if f (bytesAt s.mem ((arg s 1).setWidth 64) n) (bytesAt s.mem ((arg s 2).setWidth 64) n) =
        List.replicate n 0 then 0 else 1

/-- What two runs agree on: the stack pointer and the arguments. -/
def Pub (s₁ s₂ : State) : Prop :=
  s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3

/-- The exchange function's contract on x86, for a callee using `cs` bytes of stack. -/
def exContract (n w cs : Nat) (f : List Byte → List Byte → List Byte) : Contract isa where
  pre := Pre n w (20 + cs)
  post := ExPost n f
  pub := Pub

/-- The callee, by its contract `k`. -/
structure Callee (n w cs : Nat) (f : List Byte → List Byte → List Byte) (c : Prog isa) (k : Contract isa) :
    Prop where
  hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  hct : ConstantTime isa k.pre k.pub c
  pre : ∀ s, Pre n w cs s → k.pre s
  post : ∀ s s', k.post s s' →
    bytesAt s'.mem ((arg s 0).setWidth 64) n =
      f (bytesAt s.mem ((arg s 1).setWidth 64) n) (bytesAt s.mem ((arg s 2).setWidth 64) n)
  pub : ∀ s₁ s₂, Pub s₁ s₂ → k.pub s₁ s₂
  noSp : NoSp c
  depth : stackUse c ≤ cs

theorem Pre.top {n w S : Nat} {s : State} (h : Pre n w S s) : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Pre.stk {n w S : Nat} {s : State} (h : Pre n w S s) : S ≤ (s.gpr .esp).toNat :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' := Covers.of_mem h

/-! ## The frame -/

section
variable {n w cs : Nat} {s : State}

/-- The frame's base, `E - 16`, as a 64-bit address. -/
abbrev F (s : State) : Addr := (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64

theorem e16 (h : Pre n w (20 + cs) s) : (s.gpr .esp - BitVec.ofNat 32 16).toNat = (s.gpr .esp).toNat - 16 :=
  sub_toNat (by have := h.stk; omega)

/-- The frame's word `i`, and argument `i`, as addresses. -/
theorem fword (h : Pre n w (20 + cs) s) {d : Nat} (hd : d ≤ 12) :
    addr (s.gpr .esp - BitVec.ofNat 32 16) d = F s + BitVec.ofNat 64 d := by
  have := e16 h
  have := h.top
  exact addr_eq (by omega)

theorem aword {i : Nat} :
    addr (s.gpr .esp - BitVec.ofNat 32 16) (20 + 4 * i) = argAddr s i := by
  simp only [addr, argAddr]
  congr 1
  rw [show 20 + 4 * i = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

theorem w64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))

theorem add32_toNat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem argAddr_toNat (h : Pre n w (20 + cs) s) {i : Nat} (hi : i < 4) :
    (argAddr s i).toNat = (s.gpr .esp).toNat + 4 + 4 * i := by
  have := h.top
  rw [argAddr, w64_toNat, add32_toNat (by omega)]; omega

theorem F_toNat (h : Pre n w (20 + cs) s) : (F s).toNat = (s.gpr .esp).toNat - 16 := by
  rw [F, w64_toNat, e16 h]

theorem frR_args (h : Pre n w (20 + cs) s) : (⟨F s, 16⟩ : Region).Disjoint (argR s) := by
  have := h.stk
  refine Offset.disjoint_of_le ?_ ?_
  · show (F s).toNat + 16 ≤ (argAddr s 0).toNat
    rw [F_toNat h, argAddr_toNat h (by decide)]; omega
  · show (argAddr s 0).toNat + 16 ≤ 2 ^ 64
    rw [argAddr_toNat h (by decide)]; omega

end

/-! ## The copy of the arguments -/

section
variable {n w cs : Nat} {s : State}

/-- The frame is the 16 bytes below `E`. -/
theorem frame_eq : (⟨F s, 16⟩ : Region) = below (s.gpr .esp) 16 := rfl

theorem argR_word (h : Pre n w (20 + cs) s) {i : Nat} (hi : i < 4) : (argR s).Contains (argAddr s i) 4 := by
  simp only [Region.Contains]
  have e₁ := argAddr_toNat h hi
  have e₀ := argAddr_toNat h (i := 0) (by decide)
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, e₁, e₀]; omega), e₁, e₀]
  omega

theorem frame_word {i : Nat} (hi : i < 4) : (⟨F s, 16⟩ : Region).Contains (F s + BitVec.ofNat 64 (4 * i)) 4 :=
  Offset.contains_base _ (by omega) (by omega)

/-- One argument copied: `mov eax, [esp + 20 + 4 i]`, `mov [esp + 4 i], eax`. -/
theorem copy_step (h : Pre n w (20 + cs) s) {i : Nat} (hi : i < 4) {u : State}
    (hsp : u.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨F s, 16⟩ :: s.wr) (hf : Frame [⟨F s, 16⟩] s.mem u.mem) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u', u'.mem = u.mem.writeW (F s + BitVec.ofNat 64 (4 * i)) (arg s i) →
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) → u'.rd = u.rd → u'.wr = u.wr → WP isa (.block is) u' Q) :
    WP isa (.block (.mov .eax (.mem ⟨.esp, 20 + 4 * i⟩) :: .store ⟨.esp, 4 * i⟩ .eax :: is)) u Q := by
  have hrd' := h.1
  refine wp_ldm (B := s.gpr .esp - BitVec.ofNat 32 16) (o := 20 + 4 * i) hsp
    (by rw [aword]; exact ⟨argR s, List.mem_append_left _ (by rw [hrd, hrd']; simp), argR_word h hi⟩)
    fun u₁ v₁ => ?_
  refine wp_stm (B := s.gpr .esp - BitVec.ofNat 32 16) (o := 4 * i) (by rw [v₁.other _ (by decide), hsp])
    (by rw [fword h (by omega), v₁.wr, hwr]; exact ⟨_, List.mem_cons_self .., frame_word hi⟩) fun u₂ v₂ => ?_
  refine k u₂ ?_ (fun r hr => by rw [v₂.gpr, v₁.other r hr]) (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr])
  rw [v₂.mem, v₁.mem, v₁.gpr, aword, fword h (by omega)]
  congr 1
  rw [Frame.readW hf (r := argR s) (argR_word h hi) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (frR_args h).symm) (by decide)]
  rfl

/-- The memory once the arguments are copied to the frame. -/
abbrev cMem (s : State) : Mem :=
  (((s.mem.writeW (F s + BitVec.ofNat 64 (4 * 0)) (arg s 0)).writeW (F s + BitVec.ofNat 64 (4 * 1)) (arg s 1)).writeW
    (F s + BitVec.ofNat 64 (4 * 2)) (arg s 2)).writeW (F s + BitVec.ofNat 64 (4 * 3)) (arg s 3)

theorem cMem_frame : Frame [⟨F s, 16⟩] s.mem (cMem s) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (frame_word (by decide))).writeW
    (List.mem_singleton_self _) _ (frame_word (by decide))).writeW (List.mem_singleton_self _) _
    (frame_word (by decide))).writeW (List.mem_singleton_self _) _ (frame_word (by decide))

end

/-- Once the arguments are copied. -/
structure Copied (s e : State) : Prop where
  mem : e.mem = cMem s
  gpr : ∀ r, r ≠ .eax → r ≠ .esp → e.gpr r = s.gpr r
  esp : e.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16
  rd : e.rd = s.rd
  wr : e.wr = ⟨F s, 16⟩ :: s.wr

theorem copied_wp {n w cs : Nat} {s : State} (h : Pre n w (20 + cs) s) :
    WP isa (.block copyArgs) (allocFrame 16 s) (Copied s) := by
  have a0 : (allocFrame 16 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := allocFrame_esp _ _
  unfold copyArgs
  refine copy_step (i := 0) h (by decide) a0 rfl rfl (Frame.refl _ _) fun u₁ m₁ g₁ r₁ w₁ => ?_
  have f₁ : Frame [⟨F s, 16⟩] s.mem u₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (frame_word (by decide))
  refine copy_step (i := 1) h (by decide) (by rw [g₁ _ (by decide), a0]) r₁ w₁ f₁ fun u₂ m₂ g₂ r₂ w₂ => ?_
  have f₂ : Frame [⟨F s, 16⟩] s.mem u₂.mem := by
    rw [m₂]; exact f₁.writeW (List.mem_singleton_self _) _ (frame_word (by decide))
  refine copy_step (i := 2) h (by decide) (by rw [g₂ _ (by decide), g₁ _ (by decide), a0]) (r₂.trans r₁)
    (w₂.trans w₁) f₂ fun u₃ m₃ g₃ r₃ w₃ => ?_
  have f₃ : Frame [⟨F s, 16⟩] s.mem u₃.mem := by
    rw [m₃]; exact f₂.writeW (List.mem_singleton_self _) _ (frame_word (by decide))
  refine copy_step (i := 3) h (by decide) (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), a0])
    (r₃.trans (r₂.trans r₁)) (w₃.trans (w₂.trans w₁)) f₃ fun u₄ m₄ g₄ r₄ w₄ => WP.block_nil ?_
  refine ⟨by rw [m₄, m₃, m₂, m₁]; rfl, fun r ha hs => ?_, ?_, ?_, ?_⟩
  · rw [g₄ r ha, g₃ r ha, g₂ r ha, g₁ r ha, allocFrame_gpr _ _ hs]
  · rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), a0]
  · rw [r₄, r₃, r₂, r₁]; rfl
  · rw [w₄, w₃, w₂, w₁]; rfl

/-! ## Regions by their bounds -/

theorem sub_of_toNat {r R : Region} (h1 : R.base.toNat ≤ r.base.toNat)
    (h2 : r.base.toNat + r.len ≤ R.base.toNat + R.len) (h3 : R.base.toNat + R.len ≤ 2 ^ 64) : r.Sub R := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have e : x - R.base = (x - r.base) + (r.base - R.base) := by bv_omega
  rw [e, BitVec.toNat_add, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h1)]
  rw [Nat.mod_eq_of_lt (by have := r.base.isLt; omega)]
  omega

theorem sub32_toNat {x : BitVec 32} {k : Nat} (h : k ≤ x.toNat) : ((x - BitVec.ofNat 32 k).setWidth 64).toNat =
    x.toNat - k := by
  rw [w64_toNat, sub_toNat h]

section
variable {n w cs : Nat} {s : State}

/-- The stack below `E` we may use, by the bounds of its base. -/
theorem stk_toNat (h : Pre n w (20 + cs) s) :
    (stkR s (20 + cs)).base.toNat = (s.gpr .esp).toNat - (20 + cs) := by
  show ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 (20 + cs)).toNat = _
  have := h.stk
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, w64_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := (s.gpr .esp).isLt; omega)]; omega), w64_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]

/-- A region of the stack below `E`, by its bounds. -/
theorem in_stk (h : Pre n w (20 + cs) s) {r : Region} (h1 : (s.gpr .esp).toNat - (20 + cs) ≤ r.base.toNat)
    (h2 : r.base.toNat + r.len ≤ (s.gpr .esp).toNat) : r.Sub (stkR s (20 + cs)) := by
  have := h.stk
  have := h.top
  refine sub_of_toNat (by rw [stk_toNat h]; exact h1) (by rw [stk_toNat h]; show _ ≤ _ - _ + (20 + cs); omega)
    (by rw [stk_toNat h]; show _ - _ + (20 + cs) ≤ _; omega)

end

/-! ## The call -/

section
variable {n w cs : Nat} {s : State}

theorem word_sep {i j : Nat} (hi : i < 4) (hj : j < 4) (hij : i ≠ j) :
    Mem.Sep (F s + BitVec.ofNat 64 (4 * i)) (32 / 8) (F s + BitVec.ofNat 64 (4 * j)) (32 / 8) :=
  Region.Disjoint.sep (Offset.disjoint (F s) (d := 4 * i) (n := 4) (e := 4 * j) (k := 4) (by omega) (by omega)
    (by omega)) (Region.contains_self _ _) (Region.contains_self _ _)

theorem cMem_word {j : Nat} (hj : j < 4) : (cMem s).readW (F s + BitVec.ofNat 64 (4 * j)) 32 = arg s j := by
  match j, hj with
  | 3, _ => exact Mem.readW_writeW_self32 _ _ _
  | 2, _ =>
    rw [cMem, Mem.readW_writeW_sep (word_sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  | 1, _ =>
    rw [cMem, Mem.readW_writeW_sep (word_sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (word_sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  | 0, _ =>
    rw [cMem, Mem.readW_writeW_sep (word_sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (word_sep (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (word_sep (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

/-- The callee's entry, with the regions it is given. -/
abbrev cEntry (s e : State) : State := e.callEntry.withRegions [scR n s, ptR n s, ⟨F s, 16⟩] s.wr

theorem cEntry_esp {e : State} (he : Copied s e) :
    (cEntry (n := n) s e).gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 - 4 := by
  rw [State.withRegions_gpr, State.callEntry_esp, he.esp]

theorem cEntry_espNat (h : Pre n w (20 + cs) s) {e : State} (he : Copied s e) :
    ((cEntry (n := n) s e).gpr .esp).toNat = (s.gpr .esp).toNat - 20 := by
  have := h.stk
  rw [cEntry_esp he, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, sub_toNat (by rw [e16 h]; omega), e16 h]
  omega

theorem cEntry_arg (h : Pre n w (20 + cs) s) {e : State} (he : Copied s e) {j : Nat} (hj : j < 4) :
    arg (cEntry (n := n) s e) j = arg s j := by
  have := h.stk
  have := h.top
  show arg e.callEntry j = _
  rw [arg_callEntry (by rw [he.esp, e16 h]; omega) (by rw [he.esp, e16 h]; omega),
    show (e.gpr .esp + BitVec.ofNat 32 (4 * j)).setWidth 64 = addr (e.gpr .esp) (4 * j) from rfl, he.esp,
    fword h (by omega), he.mem, cMem_word hj]

theorem cEntry_argAddr {e : State} (he : Copied s e) : argAddr (cEntry (n := n) s e) 0 = F s := by
  show argAddr e.callEntry 0 = _
  rw [argAddr_callEntry, he.esp, Nat.mul_zero, BitVec.add_zero]

theorem cEntry_pre (h : Pre n w (20 + cs) s) {e : State} (he : Copied s e) : Pre n w cs (cEntry (n := n) s e) := by
  have hstk := h.stk
  have htop := h.top
  have hE := cEntry_espNat h he
  have a0 := cEntry_arg h he (j := 0) (by decide)
  have a1 := cEntry_arg h he (j := 1) (by decide)
  have a2 := cEntry_arg h he (j := 2) (by decide)
  have a3 := cEntry_arg h he (j := 3) (by decide)
  have hA := cEntry_argAddr (n := n) he
  have hF := F_toNat h
  obtain ⟨rd, wr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, b0, b1, b2, b3, -, -⟩ := h
  have h' : Pre n w (20 + cs) s := ⟨rd, wr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5,
    b0, b1, b2, b3, hstk, htop⟩
  -- The callee's return address and stack, and our frame, in our stack.
  have hR : (retR (cEntry (n := n) s e)).base.toNat = (s.gpr .esp).toNat - 20 := by
    show (((cEntry (n := n) s e).gpr .esp).setWidth 64).toNat = _; rw [w64_toNat, hE]
  have hK : (stkR (cEntry (n := n) s e) cs).base.toNat = (s.gpr .esp).toNat - 20 - cs := by
    show (((cEntry (n := n) s e).gpr .esp).setWidth 64 - BitVec.ofNat 64 cs).toNat = _
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, w64_toNat, hE, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]; omega), w64_toNat, hE, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have sR : (retR (cEntry (n := n) s e)).Sub (stkR s (20 + cs)) := in_stk h' (by rw [hR]; omega) (by rw [hR]; show _ + 4 ≤ _; omega)
  have sK : (stkR (cEntry (n := n) s e) cs).Sub (stkR s (20 + cs)) := in_stk h' (by rw [hK]; omega) (by rw [hK]; show _ + cs ≤ _; omega)
  have sF : (⟨F s, 16⟩ : Region).Sub (stkR s (20 + cs)) :=
    in_stk h' (show _ ≤ (F s).toNat by rw [hF]; omega) (show (F s).toNat + 16 ≤ _ by rw [hF]; omega)
  have eA : argR (cEntry (n := n) s e) = ⟨F s, 16⟩ := by rw [argR, hA]
  have eO : outR n (cEntry (n := n) s e) = outR n s := by rw [outR, a0]
  have eS : scR n (cEntry (n := n) s e) = scR n s := by rw [scR, a1]
  have eP : ptR n (cEntry (n := n) s e) = ptR n s := by rw [ptR, a2]
  have eW : wsR w (cEntry (n := n) s e) = wsR w s := by rw [wsR, a3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eS, eP, eA]; rfl
  · rw [eO, eW]; exact wr
  · rw [eO, eS]; exact d1
  · rw [eO, eP]; exact d2
  · rw [eO, eW]; exact d3
  · rw [eO, eA]; exact k1.symm.sub_right sF
  · rw [eS, eW]; exact d5
  · rw [eP, eW]; exact d6
  · rw [eW, eA]; exact k4.symm.sub_right sF
  · rw [eO]; exact k1.sub_left sR
  · rw [eS]; exact k2.sub_left sR
  · rw [eP]; exact k3.sub_left sR
  · rw [eW]; exact k4.sub_left sR
  · rw [eA]; exact Offset.disjoint_of_le (by rw [hR, hF]; show _ + 4 ≤ _; omega) (by rw [hF]; show _ + 16 ≤ _; omega)
  · rw [eO]; exact k1.sub_left sK
  · rw [eS]; exact k2.sub_left sK
  · rw [eP]; exact k3.sub_left sK
  · rw [eW]; exact k4.sub_left sK
  · rw [eA]; exact Offset.disjoint_of_le (by rw [hK, hF]; show _ + cs ≤ _; omega) (by rw [hF]; show _ + 16 ≤ _; omega)
  · rw [a0]; exact b0
  · rw [a1]; exact b1
  · rw [a2]; exact b2
  · rw [a3]; exact b3
  · rw [hE]; omega
  · rw [hE]; omega

end

theorem bytes_keep {R : Region} {m m' : Mem} (hf : Frame [R] m m') {p : Addr} {k : Nat}
    (hd : R.Disjoint ⟨p, k⟩) (hn : p.toNat + k ≤ 2 ^ 64) : bytesAt m' p k = bytesAt m p k := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => by
    rw [List.mem_singleton.mp hr] at hc
    exact hd _ hc (Offset.contains_base _ (by omega) (by omega))

theorem contains_of_toNat {R : Region} {a : Addr} {k : Nat} (h1 : R.base.toNat ≤ a.toNat)
    (h2 : a.toNat + k ≤ R.base.toNat + R.len) : R.Contains a k := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h1)]
  omega

theorem w64_bound {x : BitVec 32} {k : Nat} (h : x.toNat + k ≤ 2 ^ 32) : (x.setWidth 64).toNat + k ≤ 2 ^ 64 := by
  rw [w64_toNat]; omega

/-- After the call: `f` of the arguments at `out`, and our arguments and return address as they were. -/
structure Called (n : Nat) (f : List Byte → List Byte → List Byte) (s z : State) : Prop where
  out : bytesAt z.mem ((arg s 0).setWidth 64) n =
    f (bytesAt s.mem ((arg s 1).setWidth 64) n) (bytesAt s.mem ((arg s 2).setWidth 64) n)
  arg0 : z.mem.readW (argAddr s 0) 32 = arg s 0
  ret : z.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
  saved : ∀ r ∈ calleeSaved, r ≠ .esp → z.gpr r = s.gpr r
  esp : z.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16
  rd : z.rd = s.rd
  wr : z.wr = ⟨F s, 16⟩ :: s.wr

theorem called_wp {n w cs : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w cs f c k) {name : String} {s e : State} (h : Pre n w (20 + cs) s) (he : Copied s e) :
    WP isa (.call name c) e (Called n f s) := by
  have hstk := h.stk
  have htop := h.top
  have hF := F_toNat h
  have hdep := hk.depth
  have hcp := cEntry_pre (n := n) h he
  obtain ⟨rd, wr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, b0, b1, b2, b3, -, -⟩ := h
  have h' : Pre n w (20 + cs) s := ⟨rd, wr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5,
    b0, b1, b2, b3, hstk, htop⟩
  have sF : (⟨F s, 16⟩ : Region).Sub (stkR s (20 + cs)) :=
    in_stk h' (show _ ≤ (F s).toNat by rw [hF]; omega) (show (F s).toNat + 16 ≤ _ by rw [hF]; omega)
  have hcov : Covers ([scR n s, ptR n s, ⟨F s, 16⟩] ++ s.wr) (e.rd ++ e.wr) := covers_mem fun r hr => by
    rw [he.rd, he.wr, rd]
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr ⊢
    rcases hr with rfl | rfl | rfl | hr <;> simp_all
  have hw : Covers s.wr e.wr := covers_mem fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ hr
  refine WP.call hk.hv hk.noSp (by rw [he.esp, e16 h']; omega) (hk.pre _ hcp) hcov hw
    fun z rd' wr' cs' fr' _ ⟨s₂, m₂, _, post₂⟩ => ?_
  have hpost := hk.post _ _ post₂
  rw [m₂, cEntry_arg h' he (by decide), cEntry_arg h' he (by decide), cEntry_arg h' he (by decide)] at hpost
  -- What the copy and the return address left of the scalar and the point.
  have hE := cEntry_espNat (n := n) h' he
  have sR : (retR (cEntry (n := n) s e)).Sub (stkR s (20 + cs)) :=
    in_stk h' (show _ ≤ (((cEntry (n := n) s e).gpr .esp).setWidth 64).toNat by rw [w64_toNat, hE]; omega)
      (show (((cEntry (n := n) s e).gpr .esp).setWidth 64).toNat + 4 ≤ _ by rw [w64_toNat, hE]; omega)
  have fc : Frame [stkR s (20 + cs)] s.mem (cEntry (n := n) s e).mem := by
    show Frame _ s.mem (e.callEntry.mem)
    rw [State.callEntry_mem, he.mem]
    refine (cMem_frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact sF⟩).writeW (List.mem_singleton_self _) _ ?_
    have e₁ : ((e.gpr .esp - 4).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
      have := hE; simp only [State.withRegions_gpr, State.callEntry_esp] at this; rw [w64_toNat, this]
    exact contains_of_toNat (by rw [stk_toNat h', e₁]; omega)
      (show ((e.gpr .esp - 4).setWidth 64).toNat + 4 ≤ (stkR s (20 + cs)).base.toNat + (20 + cs) by
        rw [stk_toNat h', e₁]; omega)
  rw [bytes_keep fc k2 (w64_bound b1), bytes_keep fc k3 (w64_bound b2)] at hpost
  -- The stack the call used.
  have sB : (below (e.gpr .esp) (stackUse c + 4)).Sub (stkR s (20 + cs)) := by
    have e₁ : (below (e.gpr .esp) (stackUse c + 4)).base.toNat = (s.gpr .esp).toNat - 16 - (stackUse c + 4) := by
      show ((e.gpr .esp - BitVec.ofNat 32 (stackUse c + 4)).setWidth 64).toNat = _
      rw [sub32_toNat (by rw [he.esp, e16 h']; omega), he.esp, e16 h']
    exact in_stk h' (by rw [e₁]; omega) (by rw [e₁]; show _ + (stackUse c + 4) ≤ _; omega)
  have keep {R : Region} (hR : R.Disjoint (stkR s (20 + cs))) (ho : R.Disjoint (outR n s))
      (hw' : R.Disjoint (wsR w s)) {a : Addr} (ha : R.Contains a 4) :
      z.mem.readW a 32 = s.mem.readW a 32 := by
    rw [Frame.readW fr' ha (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · rw [wr] at hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ho
        · exact hw'
      · rw [List.mem_singleton.mp hr]; exact hR.sub_right sB) (by decide), he.mem]
    exact Frame.readW cMem_frame ha (fun r hr => by rw [List.mem_singleton.mp hr]; exact hR.sub_right sF) (by decide)
  have retS : (retR s).Disjoint (stkR s (20 + cs)) := (Offset.disjoint_of_le (r₁ := stkR s (20 + cs))
    (r₂ := retR s) (show (stkR s (20 + cs)).base.toNat + (20 + cs) ≤ ((s.gpr .esp).setWidth 64).toNat by
      rw [stk_toNat h', w64_toNat]; omega)
    (by show ((s.gpr .esp).setWidth 64).toNat + 4 ≤ _; rw [w64_toNat]; omega)).symm
  refine ⟨hpost, ?_, ?_, fun r hr he' => ?_, ?_, rd'.trans he.rd, wr'.trans he.wr⟩
  · rw [keep k5.symm d4.symm d7.symm (argR_word h' (i := 0) (by decide))]; rfl
  · exact keep retS r1 r4 (Region.contains_self _ _)
  · rw [cs' r hr, he.gpr r (by rintro rfl; simp [calleeSaved] at hr) he']
  · rw [cs' .esp (by simp [calleeSaved]), he.esp]

/-! ## The check -/

theorem orBytes_wp (o : BitVec 32) (m : Mem) : ∀ (i : Nat), o.toNat + i ≤ 2 ^ 32 →
    ∀ (u : State) (is : List Instr) (Q : State → Prop), u.gpr .edx = o → u.mem = m →
    (∀ j < i, InRegions (u.rd ++ u.wr) (o.setWidth 64 + BitVec.ofNat 64 j) 1) →
    (∀ u', u'.gpr .ecx = u.gpr .ecx ||| (orAll m (o.setWidth 64) i).setWidth 32 → u'.gpr .edx = o →
      u'.mem = m → u'.rd = u.rd → u'.wr = u.wr →
      (∀ r, r ≠ .ecx → r ≠ .eax → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) →
    WP isa (.block (orBytes i ++ is)) u Q := by
  intro i
  induction i with
  | zero =>
    intro _ u is Q ht hm _ k
    exact k u (by simp [orAll]) ht hm rfl rfl fun _ _ _ => rfl
  | succ i ih =>
    intro ho u is Q ht hm hin k
    rw [orBytes, List.append_assoc]
    refine ih (by omega) u _ Q ht hm (fun j hj => hin j (by omega)) fun u' g1 g0 gm grd gwr go => ?_
    refine wp_movzx8 (a := o.setWidth 64 + BitVec.ofNat 64 i) (by rw [g0]; exact addr_eq (by omega))
      (by rw [grd, gwr]; exact hin i (by omega)) fun u₁ v₁ => ?_
    refine wp_or fun u₂ v₂ => ?_
    refine k u₂ ?_ ?_ ?_ ?_ ?_ fun r h1 h2 => ?_
    · rw [v₂.gpr, v₁.other _ (by decide), v₁.gpr, g1, gm, orAll, BitVec.setWidth_or, BitVec.or_assoc]
    · rw [v₂.other _ (by decide), v₁.other _ (by decide), g0]
    · rw [v₂.mem, v₁.mem, gm]
    · rw [v₂.rd, v₁.rd, grd]
    · rw [v₂.wr, v₁.wr, gwr]
    · rw [v₂.other r h1, v₁.other r h2, go r h1 h2]

/-- After the frame is freed and `out` loaded into `edx`. -/
structure Restored (n : Nat) (f : List Byte → List Byte → List Byte) (s u : State) : Prop where
  called : Called n f s u
  edx : u.gpr .edx = arg s 0

/-- The state after the frame: as the call left it, with `esp` back. -/
structure Freed (n : Nat) (f : List Byte → List Byte → List Byte) (s v : State) : Prop where
  out : bytesAt v.mem ((arg s 0).setWidth 64) n =
    f (bytesAt s.mem ((arg s 1).setWidth 64) n) (bytesAt s.mem ((arg s 2).setWidth 64) n)
  arg0 : v.mem.readW (argAddr s 0) 32 = arg s 0
  ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32
  saved : ∀ r ∈ calleeSaved, v.gpr r = s.gpr r
  rd : v.rd = s.rd
  wr : v.wr = s.wr

theorem freed_of {n : Nat} {f : List Byte → List Byte → List Byte} {s z : State} (hz : Called n f s z) :
    Freed n f s (freed 16 z) := by
  refine ⟨hz.out, hz.arg0, hz.ret, fun r hr => ?_, hz.rd, by rw [freed_wr, hz.wr]; rfl⟩
  by_cases h : r = .esp
  · subst h; rw [freed_esp, hz.esp]; exact BitVec.sub_add_cancel _ _
  · rw [freed_gpr _ _ h, hz.saved r hr h]

/-- After the check. -/
structure Checked (n : Nat) (f : List Byte → List Byte → List Byte) (s v : State) : Prop where
  freed : Freed n f s v
  eax : v.gpr .eax = if orAll v.mem ((arg s 0).setWidth 64) n = 0 then 0 else 1

theorem restored_wp {n w cs : Nat} {f : List Byte → List Byte → List Byte} {s u : State}
    (h : Pre n w (20 + cs) s) (hu : Freed n f s u) :
    WP isa (.block restore) u (fun u' => Freed n f s u' ∧ u'.gpr .edx = arg s 0) := by
  have hw0 := argR_word h (i := 0) (by decide)
  have hesp : u.gpr .esp = s.gpr .esp := hu.saved .esp (by simp [calleeSaved])
  unfold restore
  refine wp_ldm (B := s.gpr .esp) (o := 4) hesp ⟨argR s, List.mem_append_left _ (by rw [hu.rd, h.1]; simp),
    hw0⟩ fun u₁ v₁ => WP.block_nil ?_
  refine ⟨⟨by rw [v₁.mem]; exact hu.out, by rw [v₁.mem]; exact hu.arg0, by rw [v₁.mem]; exact hu.ret,
    fun r hr => by rw [v₁.other r (by rintro rfl; simp [calleeSaved] at hr)]; exact hu.saved r hr,
    by rw [v₁.rd, hu.rd], by rw [v₁.wr, hu.wr]⟩, ?_⟩
  rw [v₁.gpr]; exact hu.arg0

theorem checked_wp {n w cs : Nat} {f : List Byte → List Byte → List Byte} {s u' : State}
    (h : Pre n w (20 + cs) s) (hf : Freed n f s u') (hd : u'.gpr .edx = arg s 0) :
    WP isa (.block (check n)) u' (Checked n f s) := by
  obtain ⟨rd, wr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, b0, -, -, -, -, -⟩ := h
  unfold check
  refine wp_movi fun u₁ v₁ => ?_
  refine orBytes_wp (arg s 0) u'.mem n b0 u₁ _ _ (by rw [v₁.other _ (by decide), hd]) v₁.mem
    (fun j hj => ⟨outR n s, by rw [v₁.rd, v₁.wr, hf.rd, hf.wr, wr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩) fun y g1 _ gm grd gwr go => ?_
  refine wp_subi fun u₂ v₂ _ _ => wp_shr (by decide) fun u₃ v₃ _ => wp_xori fun u₄ v₄ =>
    wp_mov fun u₅ v₅ => WP.block_nil ?_
  have hm : u₅.mem = u'.mem := by rw [v₅.mem, v₄.mem, v₃.mem, v₂.mem, gm]
  refine ⟨⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [hm]; exact hf.out
  · rw [hm]; exact hf.arg0
  · rw [hm]; exact hf.ret
  · have h1 : r ≠ .eax := by rintro rfl; simp [calleeSaved] at hr
    have h2 : r ≠ .ecx := by rintro rfl; simp [calleeSaved] at hr
    rw [v₅.other r h1, v₄.other r h2, v₃.other r h2, v₂.other r h2, go r h2 h1, v₁.other r h2]
    exact hf.saved r hr
  · rw [v₅.rd, v₄.rd, v₃.rd, v₂.rd, grd, v₁.rd, hf.rd]
  · rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, gwr, v₁.wr, hf.wr]
  · rw [v₅.gpr, v₄.gpr, v₃.gpr, v₂.gpr, g1, v₁.gpr, hm,
      show ∀ x : BitVec 32, 0 ||| x = x from fun x => BitVec.zero_or]
    exact result_shr32 _

theorem frame_wp {n w cs : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w cs f c k) {name : String} {s : State} (h : Pre n w (20 + cs) s) :
    WP isa (.frame (.alloc 16) (.seq (.block copyArgs) (.call name c)) (.free 16)) s (Freed n f s) := by
  have hstk := h.stk
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) ?_ ?_
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact (by decide : ∀ i ∈ copyArgs, Taint.clobbers i .esp = false) i hi
    · exact hk.noSp i hi
  refine WP.seq (WP.mono (copied_wp h) fun e he => ?_)
  exact WP.mono (called_wp hk h he) fun z hz => freed_of hz

/-! ## The whole function -/

theorem exchange_wp {n w cs : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w cs f c k) {name : String} {s : State} (h : Pre n w (20 + cs) s) :
    WP isa (exchange name c n) s fun z => abiPreserved s z ∧ ExPost n f s z := by
  refine WP.seq (WP.mono (frame_wp hk h) fun u hu => ?_)
  refine WP.seq (WP.mono (restored_wp h hu) fun u' ⟨hf, hd⟩ => ?_)
  refine WP.mono (checked_wp h hf hd) fun v hv => ?_
  refine ⟨⟨hv.freed.saved, hv.freed.ret⟩, hv.freed.out, ?_⟩
  rw [BitVec.setWidth_append_eq_right, hv.eax]
  exact result_spec _ _ _ _ hv.freed.out

/-! ## Constant time -/

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (τr rs) c hc).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  RelCT.taint (A := taint) (τr rs) (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact agree_regs hr) h

theorem copied_covers {n : Nat} {s e : State} (rd : s.rd = [scR n s, ptR n s, argR s]) (he : Copied s e) :
    Covers ([scR n s, ptR n s, ⟨F s, 16⟩] ++ s.wr) (e.rd ++ e.wr) ∧ Covers s.wr e.wr :=
  ⟨covers_mem fun r hr => by
    rw [he.rd, he.wr, rd]
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr ⊢
    rcases hr with rfl | rfl | rfl | hr <;> simp_all,
   covers_mem fun r hr => by rw [he.wr]; exact List.mem_cons_of_mem _ hr⟩

theorem exchange_ct {n w cs : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa} {k : Contract isa}
    (hk : Callee n w cs f c k) {name : String}
    (ht : ∃ hc, (taint.check (τr [.esp, .edx]) (.block (check n)) hc).isSome = true) :
    ConstantTime isa (Pre n w (20 + cs)) Pub (exchange name c n) := by
  obtain ⟨_, ht⟩ := ht
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  obtain ⟨qsp, q0, q1, q2, q3⟩ := hq
  have hwr : σ₂.wr = σ₁.wr := by rw [p₁.2.1, p₂.2.1]; simp only [outR, wsR, q0, q3]
  have hF : F σ₂ = F σ₁ := by rw [F, F, qsp]
  -- The frame, with the copy and the call.
  refine rel_seq ?_ (frame_wp hk p₁) (frame_wp hk p₂) fun v₁ v₂ hv₁ hv₂ => ?_
  · refine (RelCT.frameAlloc (P := Eq2 σ₁ σ₂) (R := TT (M := isa))
      ((?_ : RelCT isa (Eq2 (allocFrame 16 σ₁) (allocFrame 16 σ₂)) _ (TT (M := isa))).mono
        (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
      (fun _ _ h => h) fun _ _ _ => trivial
    refine rel_seq (rel_taint [.esp] (by simp [allocFrame_esp, qsp]) (by taint_decide))
      (copied_wp p₁) (copied_wp p₂) fun e₁ e₂ he₁ he₂ => ?_
    refine RelCT.call hk.hv hk.hct [scR n σ₁, ptR n σ₁, ⟨F σ₁, 16⟩] σ₁.wr fun a b ⟨ha, hb⟩ => ?_
    subst ha hb
    have c₂ := cEntry_pre (n := n) p₂ he₂
    have v₂ := copied_covers p₂.1 he₂
    simp only [cEntry, scR, ptR, ← q1, ← q2, hF, hwr] at c₂ v₂
    refine ⟨hk.pre _ (cEntry_pre p₁ he₁), hk.pre _ c₂, hk.pub _ _ ?_, (copied_covers p₁.1 he₁).1,
      (copied_covers p₁.1 he₁).2, v₂.1, v₂.2, ?_⟩
    · have a₁ (j : Nat) (hj : j < 4) := cEntry_arg (n := n) p₁ he₁ hj
      have a₂ (j : Nat) (hj : j < 4) := cEntry_arg (n := n) p₂ he₂ hj
      simp only [cEntry, scR, ptR, ← q1, ← q2, hF, hwr] at a₂
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [State.withRegions_gpr, State.callEntry_esp, he₁.esp, he₂.esp, qsp]
      · rw [a₁ 0 (by decide), a₂ 0 (by decide), q0]
      · rw [a₁ 1 (by decide), a₂ 1 (by decide), q1]
      · rw [a₁ 2 (by decide), a₂ 2 (by decide), q2]
      · rw [a₁ 3 (by decide), a₂ 3 (by decide), q3]
    · rw [he₁.esp, he₂.esp, qsp]
  -- `out` back, and the check.
  have e₁ : v₁.gpr .esp = σ₁.gpr .esp := hv₁.saved .esp (by simp [calleeSaved])
  have e₂ : v₂.gpr .esp = σ₂.gpr .esp := hv₂.saved .esp (by simp [calleeSaved])
  refine rel_seq (rel_taint [.esp] (by simp [e₁, e₂, qsp]) (by taint_decide))
    (restored_wp p₁ hv₁) (restored_wp p₂ hv₂) fun u₁ u₂ ⟨hu₁, d₁⟩ ⟨hu₂, d₂⟩ => ?_
  have g₁ : u₁.gpr .esp = σ₁.gpr .esp := hu₁.saved .esp (by simp [calleeSaved])
  have g₂ : u₂.gpr .esp = σ₂.gpr .esp := hu₂.saved .esp (by simp [calleeSaved])
  exact rel_taint [.esp, .edx] (by simp [g₁, g₂, d₁, d₂, qsp, q0]) ht

/-! ## `Verified` -/

theorem exchange_correct {n w cs : Nat} {f : List Byte → List Byte → List Byte} {c : Prog isa}
    {k : Contract isa} (hk : Callee n w cs f c k) {name : String} :
    ∀ s, (exContract n w cs f).pre s →
      ∃ t s', Exec isa (exchange name c n) s t s' ∧ abiPreserved s s' ∧ (exContract n w cs f).post s s' :=
  fun _ h => by
    obtain ⟨t, s', he, ha, hp⟩ := exchange_wp hk (name := name) h
    exact ⟨t, s', he, ha, hp⟩

end VG.Proof.Xdh.X86
