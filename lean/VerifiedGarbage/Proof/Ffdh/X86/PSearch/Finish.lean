module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Steps
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Call
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Exits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The parameter search's finish (x86)

From a finished search, `finish` writes the octets consumed to `used` (64
bits), returns the status and restores the caller's `esi` (`finish_ok`):
the state's four public words, `used`, the output, the callee-saved
registers and the return address are as the contract asks (`Fin`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch saved_ne bytes_frame)
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What the contract asks after a search with the result `r`. -/
structure Fin (o : State) (r : ParameterSearchResult) (t : State) : Prop where
  eax : t.gpr .eax = BitVec.ofNat 32 r.status
  saved : ∀ q ∈ calleeSaved, t.gpr q = o.gpr q
  ret : t.mem.readW ((o.gpr .esp).setWidth 64) 32 = o.mem.readW ((o.gpr .esp).setWidth 64) 32
  output : Output (ofState o) r t.mem
  policy : Spec.Rsa.wordsAt t.mem (argumentPointer o 9) 4 =
    [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 (arg o 1).toNat,
      BitVec.ofNat 64 (parameterEntropy (arg o 3).toNat), BitVec.ofNat 64 r.requested]
  used : Spec.Rsa.wordsAt t.mem (argumentPointer o 2) 1 = [BitVec.ofNat 64 r.used]

theorem Done.st {o s : State} {r : ParameterSearchResult} (h : Done (ofState o) o r s) :
    St o doneDs (doneF (ofState o) (o.gpr .esi) r) s :=
  ⟨h.input.1, h.rd, h.wr, h.syms, h.esp, h.esi, h.saved, h.frame, h.words⟩

/-- A 64-bit word of two 32-bit halves. -/
theorem word64 {m : Mem} {a : Addr} {k : Nat} (hk : k < 2 ^ 64) (lo : m.readW a 32 = BitVec.ofNat 32 k)
    (hi : m.readW (a + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (k / 2 ^ 32)) : m.readW a 64 = BitVec.ofNat 64 k := by
  rw [Proof.Rc2.Word32.read64_pair, lo, hi]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k / 2 ^ 32 < 2 ^ 32 by omega), Nat.mod_eq_of_lt hk,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]
  omega

/-- The return address, apart from every region the run writes. -/
theorem ret_apart {o : State} (A : PSearchABI o) : ∀ r ∈ frameR o, (retR o).Disjoint r := by
  have h1 : 156 ≤ (o.gpr .esp).toNat := A.stackLow
  have hl : (retR o).Disjoint (lowR o) := by
    show Region.Disjoint ⟨(o.gpr .esp).setWidth 64, 4⟩ ⟨(o.gpr .esp).setWidth 64 - BitVec.ofNat 64 156, 156⟩
    exact Offset.base_disjoint_below _ (by omega)
  exact apart A A.retO A.retU A.retB A.retS A.retA hl

/-- A 64-bit word below `2³²`. -/
theorem word64z {m : Mem} {a : Addr} {k : Nat} (hk : k < 2 ^ 32) (lo : m.readW a 32 = BitVec.ofNat 32 k)
    (hi : m.readW (a + BitVec.ofNat 64 4) 32 = 0) : m.readW a 64 = BitVec.ofNat 64 k :=
  word64 (by omega) lo (by rw [hi, Nat.div_eq_of_lt hk]; rfl)

/-- A word of the state at offset `d`, as `wordsAt` addresses it. -/
theorem st_addr {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    addr (arg o 9) d = argumentPointer o 9 + BitVec.ofNat 64 d := Spill.addr_eq_of A.sBound hd

theorem finish_ok {o s : State} {r : ParameterSearchResult} (h : Done (ofState o) o r s) :
    WP isa (.block finish) s (Fin o r) := by
  have S := h.st
  have A := h.input.1
  have hA : Aligned doneDs := by decide
  have hS := A.sBound
  have hub := A.uBound
  obtain ⟨hk, hc, hu⟩ := h.small
  have hat := attempts_le A
  have hcap := cap_lt A
  have hR : (ofState o).randLen < 2 ^ 32 := (arg o 6).isLt
  unfold finish
  refine S.ld (Or.inr (Or.inl rfl)) (d := upOff) (by decide) (by decide) fun t₁ S₁ g₁ _ _ m₁ => ?_
  refine S₁.ld (Or.inl rfl) (d := usedOff) (by decide) (by decide) fun t₂ S₂ g₂ o₂ _ m₂ => ?_
  have ec : t₂.gpr .ecx = arg o 2 := by rw [o₂ .ecx (by decide), g₁]; rfl
  have uIn : ∀ t : State, t.wr = o.wr → ∀ d, d + 4 ≤ 8 →
      InRegions t.wr (argumentPointer o 2 + BitVec.ofNat 64 d) 4 := fun t ht d hd =>
    ⟨uR o, by rw [ht]; exact uR_mem A, Offset.contains_base _ hd (by omega)⟩
  refine wp_storeS (show t₂.ea (at_ .ecx 0) = argumentPointer o 2 + BitVec.ofNat 64 0 by
      show (t₂.gpr .ecx + BitVec.ofNat 32 0).setWidth 64 = _; rw [ec]; exact addr_eq (by omega))
    (uIn t₂ S₂.wr 0 (by decide)) fun t₃ M₃ => ?_
  refine wp_movi fun t₄ U₄ => ?_
  refine wp_storeS (show t₄.ea (at_ .ecx 4) = argumentPointer o 2 + BitVec.ofNat 64 4 by
      show (t₄.gpr .ecx + BitVec.ofNat 32 4).setWidth 64 = _
      rw [U₄.other _ (by decide), M₃.gpr, ec]; exact addr_eq (by omega))
    (by rw [U₄.wr, M₃.wr]; exact uIn t₂ S₂.wr 4 (by decide)) fun t₅ M₅ => ?_
  -- The stores at `used`.
  have mem₅ : t₅.mem = (t₂.mem.writeW (argumentPointer o 2 + BitVec.ofNat 64 0) (BitVec.ofNat 32 r.used)).writeW
      (argumentPointer o 2 + BitVec.ofNat 64 4) (0 : BitVec 32) := by
    rw [M₅.mem, U₄.gpr, U₄.mem, M₃.mem, g₂]; rfl
  have fu : Frame [uR o] t₂.mem t₅.mem := by
    rw [mem₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))
  have S₅ : St o doneDs (doneF (ofState o) (o.gpr .esi) r) t₅ := by
    refine ⟨A, M₅.rd.trans (U₄.rd.trans (M₃.rd.trans S₂.rd)), M₅.wr.trans (U₄.wr.trans (M₃.wr.trans S₂.wr)),
      M₅.syms.trans (U₄.syms.trans (M₃.syms.trans S₂.syms)), ?_, ?_, fun q hq hne => ?_,
      S₂.frame.trans (fu.mono fun r hr => ?_), S₂.words.frame hS hA fu fun r hr => ?_⟩
    · rw [M₅.gpr, U₄.other _ (by decide), M₃.gpr, S₂.esp]
    · rw [M₅.gpr, U₄.other _ (by decide), M₃.gpr, S₂.esi]
    · rw [M₅.gpr, U₄.other _ (saved_ne (Or.inl rfl) hq), M₃.gpr, S₂.saved q hq hne]
    · simp only [List.mem_singleton] at hr; subst hr; exact List.mem_append_left _ (uR_mem A)
    · simp only [List.mem_singleton] at hr; subst hr; exact A.us.symm
  refine S₅.ld (Or.inl rfl) (d := statusOff) (by decide) (by decide) fun t₆ S₆ g₆ o₆ _ m₆ => ?_
  refine wp_ldm S₆.esi (S₆.rIn (d := savedOff) (by decide)) fun t₇ U₇ => WP.block_nil ?_
  have m₇ : t₇.mem = t₅.mem := by rw [U₇.mem, m₆]
  have m₂ : t₂.mem = s.mem := by rw [m₂, m₁]
  refine ⟨?_, fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · rw [U₇.other _ (by decide), g₆]; simp [doneF, statusOff]
  · by_cases hq' : q = .esi
    · subst hq'; rw [U₇.gpr, S₆.words.get (d := savedOff) (by decide)]; simp [doneF, savedOff]
    · rw [U₇.other _ hq', S₆.saved q hq hq']
  · rw [m₇]; exact S₅.frame.readW (Region.contains_self _ _) (ret_apart A) (by decide)
  · have out := h.output
    have kx : Spec.Rsa.bytesAt t₇.mem (argumentPointer o 0) (arg o 1).toNat =
        Spec.Rsa.bytesAt s.mem (argumentPointer o 0) (arg o 1).toNat := by
      rw [m₇, ← m₂]
      exact bytes_frame fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact A.ou) (by have := A.oBound; omega)
    unfold Output at out ⊢
    split at out <;> exact kx.trans out
  · have W : ∀ d ∈ doneDs, t₇.mem.readW (addr (arg o 9) d) 32 = doneF (ofState o) (o.gpr .esi) r d := by
      intro d hd; rw [m₇]; exact S₅.words.get hd
    have hl : (arg o 1).toNat < 2 ^ 32 := (arg o 1).isLt
    have hcap' : parameterEntropy (arg o 3).toNat < 2 ^ 32 := by
      have : (ofState o).cap = parameterEntropy (arg o 3).toNat := rfl; omega
    have hc' : r.requested < 2 ^ 32 := by omega
    unfold Spec.Rsa.wordsAt
    rw [show List.range 4 = [0, 1, 2, 3] from rfl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨word64 (by omega) ?_ ?_, word64z hl ?_ ?_, word64z hcap' ?_ ?_, word64z hc' ?_ ?_⟩
    · rw [← st_addr A (d := 0) (by decide), W 0 (by decide)]; simp [doneF]
    · rw [Offset.add_add, ← st_addr A (d := 4) (by decide), W 4 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 8) (by decide), W 8 (by decide)]; simp [doneF, ofState]
    · rw [Offset.add_add, ← st_addr A (d := 12) (by decide), W 12 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 16) (by decide), W 16 (by decide)]; simp [doneF, ofState]
    · rw [Offset.add_add, ← st_addr A (d := 20) (by decide), W 20 (by decide)]; simp [doneF]
    · rw [← st_addr A (d := 24) (by decide), W 24 (by decide)]; simp [doneF]
    · rw [Offset.add_add, ← st_addr A (d := 28) (by decide), W 28 (by decide)]; simp [doneF]
  · unfold Spec.Rsa.wordsAt
    rw [show List.range 1 = [0] from rfl]
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [m₇, mem₅]
    refine word64z (by omega) ?_ ?_
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        show (8 * 0 : Nat) = 0 from rfl, Mem.readW_writeW_self32]
    · rw [show (8 * 0 : Nat) = 0 from rfl, Offset.add_add, Mem.readW_writeW_self32]

end VG.Proof.Ffdh.X86.PSearch
