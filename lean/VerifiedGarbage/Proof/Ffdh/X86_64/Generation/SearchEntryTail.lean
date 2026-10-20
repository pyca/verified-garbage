module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchEntry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout

/-! # Capture stack arguments without changing the caller's argument area -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_entry_head_args {p : SearchPublic} {s : State} (h : SearchInput p s)
    {t : State} (hm : t.mem = writeController s.mem p.control (searchHeadValues s))
    (k : Keep [.rax, .r8, .r12] s t) (j : Nat) (hj : j < 4) :
    stackArg t j = stackArg s j := by
  have hf := writeController_frame s.mem p.control (searchHeadValues s) (searchHeadValues_bound s)
  have hd : (inputArgs s).Disjoint ⟨p.control, 128⟩ := by
    cases h.2
    exact (h.1.2.2.2.2.2.1 _ (by simp)).symm
  change t.mem.readW (stackArgAddr t j) 64 = _
  have ha : stackArgAddr t j = stackArgAddr s j := by
    simp only [stackArgAddr, k.1 .rsp (by simp)]
  rw [ha, hm]
  exact hf.readW (input_arg_contains s hj) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hd) (by decide)

theorem search_entry_tail_ok {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hm : t.mem = writeController s.mem p.control (searchHeadValues s))
    (k : Keep [.rax, .r8, .r12] s t) (hr : t.gpr .r12 = p.control) :
    WP isa (.block entryTail) t fun u =>
      u.mem = writeController t.mem p.control (searchTailValues s) ∧
      Keep [.rax, .r10, .r11] t u := by
  have scr := h.control_scr (s := t) k.2.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions t.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha (j : Nat) (hj : j < 4) : InRegions (t.rd ++ t.wr) (stackArgAddr t j) 8 := by
    simpa only [k.2.1, k.2.2, stackArgAddr, k.1 .rsp (by simp)] using input_args h j hj
  have hv (j : Nat) (hj : j < 4) : t.mem.readW (stackArgAddr t j) 64 = stackArg s j :=
    search_entry_head_args h hm k j hj
  refine WP.keep [.rax, .r10, .r11] ?_ rfl
  unfold entryTail writeController searchTailValues
  simp only [List.foldl_cons, List.foldl_nil]
  have ha0 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 8) 8 := ha 0 (by decide)
  have ha1 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 16) 8 := ha 1 (by decide)
  have ha2 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 24) 8 := ha 2 (by decide)
  have hv0 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := hv 0 (by decide)
  have hv1 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := hv 1 (by decide)
  have hv2 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := hv 2 (by decide)
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul,
    hr, ha0, ha1, ha2, hv0, hv1, hv2, hs 88 (by decide), hs 104 (by decide),
    hs 120 (by decide), hs 96 (by decide)]
  rfl

theorem search_entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) s fun t =>
      t.gpr .r12 = p.control ∧
      t.mem = writeController s.mem p.control (searchEntryValues s) ∧
      Keep [.rax, .r8, .r12, .r10, .r11] s t := by
  rw [entry, WP.block_append_iff]
  refine WP.mono (search_entry_head_ok h) fun t ⟨hr, hm, k⟩ => ?_
  refine WP.mono (search_entry_tail_ok h hm k hr) fun u ⟨hu, ku⟩ => ?_
  exact ⟨(ku.gpr (by decide)).trans hr,
    by rw [hu, hm, searchEntryValues, writeController_append],
    (k.trans ku).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
