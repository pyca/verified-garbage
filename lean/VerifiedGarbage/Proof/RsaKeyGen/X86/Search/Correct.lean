module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Loop
public import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Sig

/-! # The search is correct (i686)

The push, the entry, the loop, the results (the state's words as halves and
`used`, `results_ok`) and the registers restored (`restore_ok`): the
contract's postcondition (`correct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult)
open VG.Proof.Ffdh.X86.ParamInit (writes words_halves zero_half writes_append)
open VG.Proof.Ffdh.X86.KeyInit (read_write_eq read_write_ne)

/-- The state's eight halves, for a finished search, in the order `results` stores them. -/
def stateWords (p : SearchPublic) (r : PrimeSearchResult) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 r.remaining), (2, BitVec.ofNat 32 p.len), (4, BitVec.ofNat 32 (32769 * p.len)),
    (6, BitVec.ofNat 32 r.requested), (1, 0), (3, 0), (5, 0), (7, 0)]

/-- The results stored: the state's words, then `used`. -/
def finished (p : SearchPublic) (m : Mem) (r : PrimeSearchResult) : Mem :=
  writes (writes m (p.stp.setWidth 64) (stateWords p r)) (p.up.setWidth 64) [(0, BitVec.ofNat 32 r.used), (1, 0)]

theorem writes_frame' (m : Mem) (B : Addr) (n : Nat) (hn : n < 2 ^ 64) :
    ∀ l : List (Nat × BitVec 32), (∀ p ∈ l, 4 * p.1 + 4 ≤ n) → Frame [⟨B, n⟩] m (writes m B l)
  | [] , _ => Frame.refl _ _
  | (j, v) :: l, h => by
    have hj : 4 * j + 4 ≤ n := h (j, v) (List.mem_cons_self ..)
    exact ((Frame.refl [⟨B, n⟩] m).writeW (List.mem_singleton_self _) v
      (Offset.contains_base B (by omega) (by omega))).trans
      (writes_frame' _ B n hn l fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem stateWords_bound (p : SearchPublic) (r : PrimeSearchResult) : ∀ e ∈ stateWords p r, 4 * e.1 + 4 ≤ 32 := by
  simp only [stateWords, List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem usedWords_bound (r : PrimeSearchResult) :
    ∀ e ∈ [(0, BitVec.ofNat 32 r.used), (1, (0 : BitVec 32))], 4 * e.1 + 4 ≤ 8 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl) <;> dsimp only <;> decide

/-- The results change only the state and `used`. -/
theorem finished_frame {p : SearchPublic} {o : State} (h : SearchInput p o) (m : Mem) (r : PrimeSearchResult) :
    Frame [sR o, uR o] m (finished p m r) := by
  have hs : p.stp = arg o 11 := by rw [← h.2]; rfl
  have hu : p.up = arg o 2 := by rw [← h.2]; rfl
  unfold finished
  rw [hs, hu]
  exact ((writes_frame' m _ 32 (by decide) _ (stateWords_bound p r)).mono (by simp)).trans
    ((writes_frame' _ _ 8 (by decide) _ (usedWords_bound r)).mono (by simp))

theorem arg_contains {p : SearchPublic} {o : State} (h : SearchInput p o) {i : Nat} (hi : i < 12) :
    (aR o).Contains (argAddr o i) (32 / 8) := by
  have A := h.abi
  have a0 : argAddr o 0 = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  have ai : argAddr o i = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega)
  rw [ai, show aR o = ⟨argAddr o 0, 48⟩ from rfl, a0]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem results_ok {p : SearchPublic} {o s : State} {final : PrimeSearchResult} (h : SearchDone p o final s) :
    WP isa (.block results) s fun t =>
      (t.gpr .eax = BitVec.ofNat 32 final.status ∧ t.mem = finished p s.mem final) ∧
        Keep [.eax, .ecx, .edx] s t ∧ t.syms = s.syms := by
  have hi := h.input
  have A := hi.abi
  have hb := h.toSearchBase
  have hv := hi.len_valid
  have hs : p.stp = arg o 11 := by rw [← hi.2]; rfl
  have hu : p.up = arg o 2 := by rw [← hi.2]; rfl
  have WSe (k : Nat) (hk : k < 32) :
      (arg o 11 + BitVec.ofNat 32 k).setWidth 64 = (arg o 11).setWidth 64 + BitVec.ofNat 64 k :=
    VG.Proof.MlKem.X86.ea_off (by have := A.sBound; omega)
  have WSi (k : Nat) (hk : k + 4 ≤ 32) : InRegions s.wr ((arg o 11).setWidth 64 + BitVec.ofNat 64 k) 4 :=
    ⟨sR o, by rw [hb.wr, A.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have WU (k : Nat) (hk : k < 8) : (arg o 2 + BitVec.ofNat 32 k).setWidth 64 = (arg o 2).setWidth 64 + BitVec.ofNat 64 k :=
    VG.Proof.MlKem.X86.ea_off (by have := A.uBound; omega)
  have WUi (k : Nat) (hk : k + 4 ≤ 8) : InRegions s.wr ((arg o 2).setWidth 64 + BitVec.ofNat 64 k) 4 :=
    ⟨uR o, by rw [hb.wr, A.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  -- the state's words, then `used`
  rw [show results = (results.take 13) ++ (results.drop 13) from (List.take_append_drop _ _).symm]
  refine WP.block_append (WP.mono (WP.blockKeep [.eax, .ecx, .edx]
    (Q := fun u => u.gpr .eax = 0 ∧ u.mem = writes s.mem (p.stp.setWidth 64) (stateWords p final)) ?_ (by rfl))
    fun u ⟨⟨ha, hm⟩, ku, sy⟩ => ?_)
  · simp only [results, List.take, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 1) (d := 24) rfl, hb.arg_ea (i := 11) (d := 64) rfl,
      hb.arg_in (i := 1) (by decide), hb.arg_in (i := 11) (by decide), hb.arg_val (i := 1) (by decide),
      hb.arg_val (i := 11) (by decide), hi.len_arg, execMul, h.esi, h.edi, h.ebp, h.ebx,
      show (32769 : BitVec 32).toNat = 32769 from rfl, toNat_small32 (show p.len < 2 ^ 32 by omega),
      WSe 0 (by decide), WSe 4 (by decide), WSe 8 (by decide),
      WSe 12 (by decide), WSe 16 (by decide), WSe 20 (by decide),
      WSe 24 (by decide), WSe 28 (by decide),
      WSi 0 (by decide), WSi 4 (by decide), WSi 8 (by decide),
      WSi 12 (by decide), WSi 16 (by decide), WSi 20 (by decide),
      WSi 24 (by decide), WSi 28 (by decide)]
    simp only [writes, stateWords, hs, Nat.reduceMul, Nat.mul_comm 32769]
  have hfu : Frame [sR o] s.mem u.mem := by
    rw [hm, hs]; exact writes_frame' _ _ 32 (by decide) _ (stateWords_bound p final)
  have hbu := hb.keep ku (by decide) sy (frame_apart hi A.lowS hfu hb.saved)
    (hfu.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨sR o, by simp [changes], fun _ h => h⟩)
  have v2 : u.mem.readW (argAddr o 2) 32 = arg o 2 := by
    rw [hfu.readW (arg_contains hi (i := 2) (by decide)) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact A.sa.symm) (by decide)]
    exact hb.arg_val (by decide)
  have WUi' (k : Nat) (hk : k + 4 ≤ 8) : InRegions u.wr ((arg o 2).setWidth 64 + BitVec.ofNat 64 k) 4 := by
    rw [ku.2.2]; exact WUi k hk
  refine WP.mono (WP.blockKeep [.eax, .ecx, .edx]
    (Q := fun t => t.gpr .eax = BitVec.ofNat 32 final.status ∧ t.mem = finished p s.mem final) ?_ (by rfl))
    fun t ⟨⟨ht, hmt⟩, kt, syt⟩ => ⟨⟨ht, hmt⟩, (ku.trans kt).mono (by simp), syt.trans sy⟩
  simp only [results, List.drop, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hbu.arg_ea (i := 2) (d := 28) rfl, hbu.arg_in (i := 2) (by decide), v2,
    WU 0 (by decide), WU 4 (by decide), WUi' 0 (by decide), WUi' 4 (by decide),
    (ku.gpr (by decide) : u.gpr .esi = s.gpr .esi), (ku.gpr (by decide) : u.gpr .ebx = s.gpr .ebx), h.esi, h.ebx, ha]
  simp only [finished, writes, hu, Nat.reduceMul]
  rw [hm]

end VG.Proof.RsaKeyGen.X86.Search
