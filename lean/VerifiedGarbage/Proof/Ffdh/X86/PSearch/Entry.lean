module

import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Ffdh.X86.ParamSearch
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Data
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Data

/-! # The parameter search's entry (x86)

`entry` saves the caller's `esi` in the state, points `esi` at it and keeps
the arguments the loop needs there (`keep_ok`, one argument at a time):
from the contract's precondition, a loop state with nothing consumed and the
caller's attempts (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- An entry state: the state's words at `ds` hold `f`, the memory differs from the entry's only in
the state. -/
structure Ent (o : State) (ds : List Nat) (f : Nat → BitVec 32) (s : State) : Prop where
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  syms : s.syms = o.syms
  esp : s.gpr .esp = o.gpr .esp
  esi : s.gpr .esi = arg o 9
  saved : ∀ r ∈ calleeSaved, r ≠ .esi → s.gpr r = o.gpr r
  frame : Frame [sR o] o.mem s.mem
  words : Ctl s.mem (arg o 9) ds f

/-- Argument `i`, read from an entry state. -/
theorem Ent.argSrc {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (A : PSearchABI o) (h : Ent o ds f s)
    {i : Nat} (hi : i < 10) :
    readSrc s (.mem (argAt 0 i)) = some (arg o i) := by
  have e : argAt 0 i = ⟨.esp, 4 + 4 * i⟩ := by simp [argAt, at_]
  rw [e, readSrc_mem h.esp (by rw [h.rd, h.wr]; exact ⟨_, List.mem_append_right _ (aR_mem A), arg_in A hi⟩)]
  congr 1
  exact h.frame.readW (arg_in A hi) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact A.sa.symm) (by decide)

/-- `keep i d`: argument `i` to the state's word at `d`. -/
theorem keep_ok {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (A : PSearchABI o) (h : Ent o ds f s)
    (hA : Aligned ds) {i d : Nat} (hi : i < 10) (hd : d + 4 ≤ 128) (hd4 : d % 4 = 0) {rest : List Instr}
    {Q : State → Prop} (k : ∀ t, Ent o ds (upd f d (arg o i)) t → WP isa (.block rest) t Q) :
    WP isa (.block (keep i d ++ rest)) s Q := by
  refine wp_movS (h.argSrc A hi) fun t U _ => ?_
  refine wp_storeS (st_ea ((U.other _ (by decide)).trans h.esi) d)
    (by rw [U.wr, h.wr]; exact ⟨_, sR_mem A, st_in A hd⟩) fun t' M => k t' ?_
  rw [U.gpr] at M
  refine ⟨M.rd.trans (U.rd.trans h.rd), M.wr.trans (U.wr.trans h.wr), M.syms.trans (U.syms.trans h.syms), ?_, ?_,
    fun r hr hne => ?_, ?_, ?_⟩
  · rw [M.gpr, U.other _ (by decide), h.esp]
  · rw [M.gpr, U.other _ (by decide), h.esi]
  · rw [M.gpr, U.other _ (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      first | decide | exact absurd rfl hne), h.saved r hr hne]
  · rw [M.mem, U.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ (st_in A hd)
  · rw [M.mem, U.mem]; exact h.words.write A.sBound hA hd hd4 _

/-- The halves of a 64-bit word. -/
theorem halves {m : Mem} {a : Addr} {k : Nat} (h : m.readW a 64 = BitVec.ofNat 64 k) (hk : k < 2 ^ 64) :
    m.readW a 32 = BitVec.ofNat 32 k ∧ m.readW (a + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (k / 2 ^ 32) := by
  refine ⟨(Mem.readW_lo32 h).trans ?_, (Mem.readW_hi32 h).trans ?_⟩ <;> apply BitVec.eq_of_toNat_eq
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]

/-- The state's attempts, width and cap, from the contract's precondition. -/
theorem entry_words {o : State} (A : PSearchABI o) :
    o.mem.readW (addr (arg o 9) 0) 32 = BitVec.ofNat 32 (ofState o).attempts ∧
      o.mem.readW (addr (arg o 9) 4) 32 = BitVec.ofNat 32 ((ofState o).attempts / 2 ^ 32) ∧
      o.mem.readW (addr (arg o 9) 8) 32 = BitVec.ofNat 32 (ofState o).len ∧
      o.mem.readW (addr (arg o 9) 16) 32 = BitVec.ofNat 32 (ofState o).cap := by
  have hS := A.sBound
  have e : ∀ d, d + 4 ≤ 128 → addr (arg o 9) d = argumentPointer o 9 + BitVec.ofNat 64 d :=
    fun d hd => Spill.addr_eq_of hS hd
  have k0 := halves (m := o.mem) (a := argumentPointer o 9) (k := (ofState o).attempts)
    (by simp only [ofState, BitVec.ofNat_toNat, BitVec.setWidth_eq]) (BitVec.isLt _)
  have k1 := halves A.width (by have := (arg o 1).isLt; omega)
  have k2 := halves A.cap (by unfold Spec.Ffdh.parameterEntropy; have := A.bitsHigh; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e 0 (by decide), BitVec.add_zero]; exact k0.1
  · rw [e 4 (by decide)]; exact k0.2
  · rw [e 8 (by decide)]; exact k1.1
  · rw [e 16 (by decide)]; exact k2.1

/-- The words before the entry. -/
abbrev f0 (o : State) : Nat → BitVec 32 := fun d => o.mem.readW (addr (arg o 9) d) 32

theorem entry_ok {o : State} (A : PSearchABI o) :
    WP isa (.block entry) o (Live (ofState o) o 0 (ofState o).attempts) := by
  have hA : Aligned liveDs := by decide
  have e9 : argAt 0 9 = ⟨.esp, 4 + 4 * 9⟩ := by simp [argAt, at_]
  have r9 : readSrc o (.mem (argAt 0 9)) = some (arg o 9) := by
    rw [e9, readSrc_mem rfl ⟨_, List.mem_append_right _ (aR_mem A), arg_in A (i := 9) (by decide)⟩]; rfl
  unfold entry
  simp only [List.cons_append, List.append_assoc]
  refine wp_movS r9 fun t U _ => ?_
  refine wp_storeS (show t.ea ⟨.eax, savedOff⟩ = addr (arg o 9) 32 by rw [ea_mk, U.gpr]; rfl)
    (by rw [U.wr]; exact ⟨_, sR_mem A, st_in A (d := 32) (by decide)⟩) fun t₁ M => ?_
  refine wp_movS (v := t₁.gpr .eax) rfl fun t₂ U₂ _ => ?_
  have E : Ent o liveDs (upd (f0 o) 32 (o.gpr .esi)) t₂ := by
    refine ⟨U₂.rd.trans (M.rd.trans U.rd), U₂.wr.trans (M.wr.trans U.wr), U₂.syms.trans (M.syms.trans U.syms),
      ?_, ?_, fun r hr hne => ?_, ?_, ?_⟩
    · rw [U₂.other _ (by decide), M.gpr, U.other _ (by decide)]
    · rw [U₂.gpr, M.gpr, U.gpr]
    · have h1 : r ≠ .eax := by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [U₂.other _ hne, M.gpr, U.other _ h1]
    · rw [U₂.mem, M.mem, U.other _ (by decide), U.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (st_in A (by decide))
    · rw [U₂.mem, M.mem, U.other _ (by decide), U.mem]
      exact (show Ctl o.mem (arg o 9) liveDs (f0 o) from fun _ _ => rfl).write A.sBound hA (by decide)
        (by decide) _
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine keep_ok A E hA (by decide) (by decide) (by decide) fun t E => ?_
  refine wp_movS (v := 0) rfl fun t₃ U₃ _ => ?_
  have esi₃ : t₃.gpr .esi = arg o 9 := (U₃.other _ (by decide)).trans E.esi
  have W₀ : InRegions t₃.wr (addr (arg o 9) usedOff) 4 := by
    rw [U₃.wr, E.wr]; exact ⟨_, sR_mem A, st_in A (d := 72) (by decide)⟩
  refine wp_storeS (st_ea esi₃ usedOff) W₀ fun t₄ M₄ => ?_
  refine wp_storeS (st_ea (M₄.gpr ▸ esi₃) (widthOff + 4))
    (by rw [M₄.wr, U₃.wr, E.wr]; exact ⟨_, sR_mem A, st_in A (d := 12) (by decide)⟩) fun t₅ M₅ => ?_
  refine wp_storeS (st_ea (M₅.gpr ▸ M₄.gpr ▸ esi₃) (capOff + 4))
    (by rw [M₅.wr, M₄.wr, U₃.wr, E.wr]; exact ⟨_, sR_mem A, st_in A (d := 20) (by decide)⟩) fun t₆ M₆ => ?_
  refine wp_storeS (st_ea (M₆.gpr ▸ M₅.gpr ▸ M₄.gpr ▸ esi₃) (requestOff + 4))
    (by rw [M₆.wr, M₅.wr, M₄.wr, U₃.wr, E.wr]; exact ⟨_, sR_mem A, st_in A (d := 28) (by decide)⟩) fun t₇ M₇ => ?_
  refine WP.block_nil_iff.mpr ?_
  have W := entry_words A
  simp only [ofState] at W
  have g₄ : t₄.gpr .eax = 0 := by rw [M₄.gpr, U₃.gpr]
  have g₅ : t₅.gpr .eax = 0 := by rw [M₅.gpr, g₄]
  have g₆ : t₆.gpr .eax = 0 := by rw [M₆.gpr, g₅]
  have hm : t₇.mem = (((t.mem.writeW (addr (arg o 9) usedOff) (0 : BitVec 32)).writeW
      (addr (arg o 9) (widthOff + 4)) (0 : BitVec 32)).writeW (addr (arg o 9) (capOff + 4)) (0 : BitVec 32)).writeW
      (addr (arg o 9) (requestOff + 4)) (0 : BitVec 32) := by
    rw [M₇.mem, g₆, M₆.mem, g₅, M₅.mem, g₄, M₄.mem, U₃.gpr, U₃.mem]
  have C := (((E.words.write A.sBound hA (d := usedOff) (by decide) (by decide) 0).write A.sBound hA
    (d := widthOff + 4) (by decide) (by decide) 0).write A.sBound hA (d := capOff + 4) (by decide) (by decide) 0).write
    A.sBound hA (d := requestOff + 4) (by decide) (by decide) 0
  rw [← hm] at C
  have F : Frame [sR o] o.mem t₇.mem := by
    rw [hm]
    exact (((E.frame.writeW (List.mem_singleton_self _) _ (st_in A (d := usedOff) (by decide))).writeW
      (List.mem_singleton_self _) _ (st_in A (d := widthOff + 4) (by decide))).writeW
      (List.mem_singleton_self _) _ (st_in A (d := capOff + 4) (by decide))).writeW
      (List.mem_singleton_self _) _ (st_in A (d := requestOff + 4) (by decide))
  refine ⟨⟨A, rfl⟩, Nat.zero_le _, Nat.le_refl _, M₇.rd.trans (M₆.rd.trans (M₅.rd.trans (M₄.rd.trans (U₃.rd.trans E.rd)))),
    M₇.wr.trans (M₆.wr.trans (M₅.wr.trans (M₄.wr.trans (U₃.wr.trans E.wr)))),
    M₇.syms.trans (M₆.syms.trans (M₅.syms.trans (M₄.syms.trans (U₃.syms.trans E.syms)))), ?_, ?_,
    fun r hr hne => ?_, ?_, C.congr ?_⟩
  · rw [M₇.gpr, M₆.gpr, M₅.gpr, M₄.gpr, U₃.other _ (by decide), E.esp]; rfl
  · rw [M₇.gpr, M₆.gpr, M₅.gpr, M₄.gpr, esi₃]; rfl
  · have h1 : r ≠ .eax := by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [M₇.gpr, M₆.gpr, M₅.gpr, M₄.gpr, U₃.other _ h1, E.saved r hr hne]
  · exact F.mono fun r hr => List.mem_append_left _ (by
      simp only [List.mem_singleton] at hr; subst hr; exact sR_mem A)
  · simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false]
    rintro d (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [upd, liveF, ofState, outOff, upOff, bitsOff, genOff, randOff, leftOff, scratchOff, slenOff, usedOff,
        widthOff, capOff, requestOff] <;> simp [W.1, W.2.1, W.2.2.1, W.2.2.2]

end VG.Proof.Ffdh.X86.PSearch
