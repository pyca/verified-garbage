module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Ends
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Ends
meta import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.MlKem.X86.Common

-- separate module: the candidate's arguments, whose stores build in parallel with the rest of the search

/-! # The candidate's frame of arguments (i686)

The search's 216 bytes of stack, at offsets of `low o`: the candidate's own
152, the call's return address at 152, the frame of the candidate's eleven
arguments at 156 (`frR`) and the saved registers at 200. `arguments` stores
the arguments there (`arguments_ok`), each read from the search's own.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86 VG.X86.Wp
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Proof.Mont.X86 (wp_storeS wp_movS)

/-- The base of the stack the search uses. -/
abbrev low (o : State) : Addr := (o.gpr .esp).setWidth 64 - 216#64

theorem low_toNat {o : State} (A : SearchABI o) : (low o).toNat = (o.gpr .esp).toNat - 216 := by
  have : 216 ≤ (o.gpr .esp).toNat := A.stackLow
  have := (o.gpr .esp).isLt
  simp only [low, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A word at `d` above a stack pointer `k ≤ 216` bytes below the entry's. -/
theorem addr_sub {o : State} (A : SearchABI o) {k d : Nat} (hk : k ≤ 216) (hd : d < k + 52) :
    addr (o.gpr .esp - BitVec.ofNat 32 k) d = low o + BitVec.ofNat 64 (216 - k + d) := by
  have h1 : 216 ≤ (o.gpr .esp).toNat := A.stackLow
  have h2 := A.stackBound
  have hl := low_toNat A
  apply BitVec.eq_of_toNat_eq
  simp only [addr, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, hl]
  omega

/-- A range at offsets of `low o` lies in the stack the search uses. -/
theorem low_sub {o : State} {d n : Nat} (h : d + n ≤ 216) : Region.Sub ⟨low o + BitVec.ofNat 64 d, n⟩ (lowR o) :=
  Offset.sub_base _ h

/-- The frame of the candidate's arguments. -/
abbrev frR (o : State) : Region := ⟨low o + BitVec.ofNat 64 156, 44⟩

/-- The frame the search pushes, at its offset. -/
theorem push_eq {p : SearchPublic} {o : State} (h : SearchInput p o) :
    below p.sp 16 = ⟨low o + BitVec.ofNat 64 200, 16⟩ := by
  have A := h.abi
  rw [h.sp_eq]
  have e := addr_sub A (k := 16) (d := 0) (by decide) (by decide)
  simp only [addr, BitVec.add_zero] at e
  change (⟨(o.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ : Region) = _
  rw [e]

/-- The saved registers' words, at their offsets. -/
theorem saved_addr {p : SearchPublic} {o : State} (h : SearchInput p o) {i : Nat} (hi : i < 4) :
    (p.S1 + BitVec.ofNat 32 (4 * i)).setWidth 64 = low o + BitVec.ofNat 64 (200 + 4 * i) := by
  have A := h.abi
  rw [SearchPublic.S1, h.sp_eq]
  exact addr_sub A (by decide) (by omega)

/-- A state in the candidate's frame: `SearchBase` but for the stack pointer
and the frame's region, with the registers but `eax` those of `s₀`, the
state before the frame. -/
structure Fr (p : SearchPublic) (o s₀ s : State) : Prop where
  input : SearchInput p o
  rd : s.rd = o.rd
  wr : s.wr = frR o :: below p.sp 16 :: o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = p.S2
  keep : ∀ r, r ≠ .eax → r ≠ .esp → s.gpr r = s₀.gpr r
  saved : Saved s.mem p.S1 o
  frame : Frame (changes o) o.mem s.mem

theorem S2_eq (p : SearchPublic) :
    p.S2 = p.S1 - BitVec.ofNat 32 44 := by
  rw [SearchPublic.S2, SearchPublic.S1, BitVec.sub_sub]; rfl

theorem SearchBase.alloc {p : SearchPublic} {o s : State} (h : SearchBase p o s) :
    Fr p o s (allocFrame 44 s) := by
  have A := h.input.abi
  refine ⟨h.input, h.rd, ?_, h.syms, by rw [allocFrame_esp, h.sp, S2_eq p],
    fun r _ hsp => allocFrame_gpr _ _ hsp, h.saved, h.frame⟩
  change ⟨(s.gpr .esp - BitVec.ofNat 32 44).setWidth 64, 44⟩ :: s.wr = _
  rw [h.wr, h.sp, ← S2_eq p, SearchPublic.S2, h.input.sp_eq]
  have e := addr_sub A (k := 60) (d := 0) (by decide) (by decide)
  simp only [addr, BitVec.add_zero] at e
  rw [e]

/-- The candidate's arguments for `used` octets consumed. -/
def callArg (o : State) (used : Nat) (j : Nat) : BitVec 32 :=
  if j = 7 then arg o 7 + BitVec.ofNat 32 used else
  if j = 8 then arg o 8 - BitVec.ofNat 32 used else arg o j

/-- The first `k` arguments are in the frame. -/
def ArgsAt (o : State) (used k : Nat) (m : Mem) : Prop :=
  ∀ j < k, m.readW (low o + BitVec.ofNat 64 (156 + 4 * j)) 32 = callArg o used j

/-- The search's argument `i`, from the candidate's frame. -/
theorem Fr.load {p : SearchPublic} {o s₀ s : State} (h : Fr p o s₀ s) {i : Nat} (hi : i < 12) :
    readSrc s (.mem (param callWords i)) = some (arg o i) := by
  have A := h.input.abi
  have ea : s.ea (param callWords i) = argAddr o i := by
    change addr (s.gpr .esp) (4 + 4 * i + 4 * (4 + 11)) = _
    rw [h.esp, SearchPublic.S2, h.input.sp_eq]
    unfold argAddr
    change ((o.gpr .esp - BitVec.ofNat 32 60) + BitVec.ofNat 32 (4 + 4 * i + 60)).setWidth 64 = _
    rw [BitVec.ofNat_add (4 + 4 * i) 60, BitVec.add_comm (BitVec.ofNat 32 (4 + 4 * i)), ← BitVec.add_assoc,
      BitVec.sub_add_cancel]
  have hin : InRegions (s.rd ++ s.wr) (argAddr o i) 4 := by
    have a0 : argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
    have ai : argAddr o i = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
      VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
    refine ⟨aR o, ?_, ?_⟩
    · rw [h.rd, h.wr, A.wr]; simp
    · rw [ai, show aR o = ⟨argAddr o 0, 48⟩ from rfl, a0]
      exact Offset.contains _ (by omega) (by omega) (by omega)
  change s.load32 (s.ea _) = _
  simp only [State.load32, ea, hin, ↓reduceIte]
  rw [h.input.arg_frame h.frame hi]; rfl

/-- `mov [esp + 4 j], eax`, argument `j` in `eax`. -/
theorem store_ok {p : SearchPublic} {o s₀ s : State} {used : Nat} (h : Fr p o s₀ s)
    {j : Nat} (hj : j < 11) (hv : s.gpr .eax = callArg o used j)
    (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr p o s₀ t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (.store (at_ .esp (4 * j)) .eax :: rest)) s Q := by
  have A := h.input.abi
  have hl := low_toNat A
  have hb := A.stackBound
  have hlow := A.stackLow
  have ea : addr (s.gpr .esp) (4 * j) = low o + BitVec.ofNat 64 (156 + 4 * j) := by
    rw [h.esp, SearchPublic.S2, h.input.sp_eq, addr_sub A (by decide) (by omega)]
  have win : (frR o).Contains (low o + BitVec.ofNat 64 (156 + 4 * j)) 4 :=
    Offset.contains _ (by omega) (by omega) (by omega)
  refine wp_storeS (show s.ea ⟨.esp, 4 * j⟩ = _ by rw [ea_mk, ea])
    (by rw [h.wr]; exact ⟨_, List.mem_cons_self .., win⟩) fun t' M => k t' ?_ ?_
  · have lc : (lowR o).Contains (low o + BitVec.ofNat 64 (156 + 4 * j)) 4 :=
      Offset.contains_base _ (by omega) (by omega)
    have fr : Frame [lowR o] s.mem t'.mem := by
      rw [M.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ lc
    refine ⟨h.input, M.rd.trans h.rd, M.wr.trans h.wr, M.syms.trans h.syms, by rw [M.gpr, h.esp],
      fun r hr hsp => by rw [M.gpr, h.keep r hr hsp], ?_, h.frame.trans (fr.mono fun r hr => ?_)⟩
    · obtain ⟨s0, s1, s2, s3⟩ := h.saved
      have keep (i : Nat) (hi : i < 4) : t'.mem.readW ((p.S1 + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
          s.mem.readW ((p.S1 + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 := by
        rw [M.mem, saved_addr h.input hi]
        exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
      exact ⟨(keep 0 (by decide)).trans s0, (keep 1 (by decide)).trans s1, (keep 2 (by decide)).trans s2,
        (keep 3 (by decide)).trans s3⟩
    · simp only [List.mem_singleton] at hr; subst hr
      simp [changes, h.input.low_eq]
  · intro i hi
    rw [M.mem]
    by_cases hij : i = j
    · subst hij; rw [Mem.readW_writeW_self32, hv]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact ha i (by omega)

theorem Fr.eax {p : SearchPublic} {o s₀ s t : State} (h : Fr p o s₀ s) {v : BitVec 32} (U : Upd s t .eax v) :
    Fr p o s₀ t :=
  ⟨h.input, U.rd.trans h.rd, U.wr.trans h.wr, U.syms.trans h.syms, by rw [U.other _ (by decide), h.esp],
    fun r hr hsp => by rw [U.other _ hr, h.keep r hr hsp], by rw [U.mem]; exact h.saved,
    by rw [U.mem]; exact h.frame⟩

/-- `pass j []`: argument `j` as the search has it. -/
theorem pass_ok {p : SearchPublic} {o s₀ s : State} {used : Nat} (h : Fr p o s₀ s) {j : Nat} (hj : j < 11)
    (hc : callArg o used j = arg o j) (ha : ArgsAt o used j s.mem) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Fr p o s₀ t → ArgsAt o used (j + 1) t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (pass j [] ++ rest)) s Q := by
  show WP isa (.block (.mov .eax (.mem (param callWords j)) :: .store (at_ .esp (4 * j)) .eax :: rest)) s Q
  refine wp_movS (h.load (by omega)) fun t U _ => ?_
  exact store_ok (h.eax U) hj (by rw [U.gpr, hc]) (by rw [U.mem]; exact ha) k

theorem arguments_ok {p : SearchPublic} {o s₀ s : State} {used : Nat} (h : Fr p o s₀ s)
    (hsi : s₀.gpr .esi = BitVec.ofNat 32 used) :
    WP isa (.block arguments) s fun t => Fr p o s₀ t ∧ ArgsAt o used 11 t.mem := by
  have esi : ∀ t, Fr p o s₀ t → t.gpr .esi = BitVec.ofNat 32 used := fun t ht =>
    (ht.keep .esi (by decide) (by decide)).trans hsi
  show WP isa (.block (pass 0 [] ++ (pass 1 [] ++ (pass 2 [] ++ (pass 3 [] ++ (pass 4 [] ++ (pass 5 [] ++ (pass 6 [] ++ (pass 7 [.alu .add .eax (.reg .esi)] ++ (pass 8 [.alu .sub .eax (.reg .esi)] ++ (pass 9 [] ++ (pass 10 [] ++ [])))))))))))) s _
  refine pass_ok (used := used) h (j := 0) (by decide) rfl (fun _ h => absurd h (Nat.not_lt_zero _)) fun t h a => ?_
  refine pass_ok h (j := 1) (by decide) rfl a fun t h a => ?_
  refine pass_ok h (j := 2) (by decide) rfl a fun t h a => ?_
  refine pass_ok h (j := 3) (by decide) rfl a fun t h a => ?_
  refine pass_ok h (j := 4) (by decide) rfl a fun t h a => ?_
  refine pass_ok h (j := 5) (by decide) rfl a fun t h a => ?_
  refine pass_ok h (j := 6) (by decide) rfl a fun t h a => ?_
  -- the rest of the tape: its pointer and its length
  show WP isa (.block (.mov .eax (.mem (param callWords 7)) :: .alu .add .eax (.reg .esi) ::
    .store (at_ .esp (4 * 7)) .eax :: _)) t _
  refine wp_movS (h.load (by decide)) fun t₁ U₁ _ => wp_add fun t₂ U₂ _ => ?_
  have h₂ := (h.eax U₁).eax U₂
  refine store_ok h₂ (j := 7) (by decide) (by rw [U₂.gpr, U₁.gpr, U₁.other _ (by decide), esi t h]; rfl)
    (by rw [U₂.mem, U₁.mem]; exact a) fun t h a => ?_
  show WP isa (.block (.mov .eax (.mem (param callWords 8)) :: .alu .sub .eax (.reg .esi) ::
    .store (at_ .esp (4 * 8)) .eax :: _)) t _
  refine wp_movS (h.load (by decide)) fun t₁ U₁ _ => wp_sub fun t₂ U₂ _ => ?_
  have h₂ := (h.eax U₁).eax U₂
  refine store_ok h₂ (j := 8) (by decide) (by rw [U₂.gpr, U₁.gpr, U₁.other _ (by decide), esi t h]; rfl)
    (by rw [U₂.mem, U₁.mem]; exact a) fun t h a => ?_
  refine pass_ok h (j := 9) (by decide) rfl a fun t h a => ?_
  refine pass_ok h (j := 10) (by decide) rfl a fun t h a => ?_
  exact WP.block_nil ⟨h, a⟩

end VG.Proof.RsaKeyGen.X86.Search
