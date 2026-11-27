module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTStep
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTStep
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTBase
public import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTBase
meta import VerifiedGarbage.Proof.Ffdh.X86.ParamInit
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.EntropyRequest

/-! ### `RsaKeyGen.X86.Search.Correct`, which only this module used -/

section

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
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult)
open VG.Proof.Ffdh.X86.ParamInit (writes words_halves zero_half writes_append)
open VG.Proof.Ffdh.X86.KeyInit (read_write_eq read_write_ne)

/-- The state's eight halves, for a finished search, in the order `results` stores them. -/
def stateWords (p : SearchPublic) (r : PrimeSearchResult) : List (Nat × BitVec 32) :=
  [(0, BitVec.ofNat 32 r.remaining), (2, BitVec.ofNat 32 p.len), (4, BitVec.ofNat 32 (32769 * p.len)),
    (6, BitVec.ofNat 32 (requested p.len r)), (1, 0), (3, 0), (5, 0), (7, 0)]

/-- The results stored: the state's words, then `used`. -/
def finished (p : SearchPublic) (m : Mem) (r : PrimeSearchResult) : Mem :=
  writes (writes m (p.stp.setWidth 64) (stateWords p r)) (p.up.setWidth 64) [(0, BitVec.ofNat 32 r.used), (1, 0)]

theorem writes_frame' (m : Mem) (B : Addr) (n : Nat) (hn : n < 2 ^ 64) :
    ∀ l : List (Nat × BitVec 32), (∀ p ∈ l, 4 * p.1 + 4 ≤ n) → Frame [⟨B, n⟩] m (writes m B l)
  | [] , _ => Frame.refl _ _
  | (j, v) :: l, h => by
    have hj : 4 * j + 4 ≤ n := h (j, v) (List.mem_cons_self ..)
    exact ((Frame.refl [⟨B, n⟩] m).writeW (List.mem_singleton_self _) v
      (Offset.contains_base B (by omega_using [hj]) (by omega_using [hn, hj]))).trans
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
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega_using [this])
  have ai : argAddr o i = (o.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    VG.Proof.MlKem.X86.ea_off (by have := A.stackBound; omega_using [hi, this])
  rw [ai, show aR o = ⟨argAddr o 0, 48⟩ from rfl, a0]
  exact Offset.contains _ (by omega_using []) (by omega_using [hi]) (by omega_using [])

/-- The state's words. -/
theorem results_head_ok {p : SearchPublic} {o s : State} {final : PrimeSearchResult} (h : SearchDone p o final s) :
    WP isa (.block (results.take 13)) s fun u =>
      (u.gpr .eax = 0 ∧ u.mem = writes s.mem (p.stp.setWidth 64) (stateWords p final) ∧ SearchBase p o u) ∧
        Keep [.eax, .ecx, .edx] s u ∧ u.syms = s.syms := by
  have hi := h.input
  have A := hi.abi
  have hb := h.toSearchBase
  have hv := hi.len_valid
  have hs : p.stp = arg o 11 := by rw [← hi.2]; rfl
  have WSe (k : Nat) (hk : k < 32) :
      (arg o 11 + BitVec.ofNat 32 k).setWidth 64 = (arg o 11).setWidth 64 + BitVec.ofNat 64 k :=
    VG.Proof.MlKem.X86.ea_off (by have := A.sBound; omega_using [hk, this])
  have WSi (k : Nat) (hk : k + 4 ≤ 32) : InRegions s.wr ((arg o 11).setWidth 64 + BitVec.ofNat 64 k) 4 :=
    ⟨sR o, by rw [hb.wr, A.wr]; simp, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  refine WP.mono (WP.blockKeep [.eax, .ecx, .edx]
    (Q := fun u => u.gpr .eax = 0 ∧ u.mem = writes s.mem (p.stp.setWidth 64) (stateWords p final)) ?_ (by rfl))
    fun u ⟨⟨ha, hm⟩, ku, sy⟩ => ⟨⟨ha, hm, ?_⟩, ku, sy⟩
  · simp only [results, List.take, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 1) (d := 24) rfl, hb.arg_ea (i := 11) (d := 64) rfl,
      hb.arg_in (i := 1) (by decide), hb.arg_in (i := 11) (by decide), hb.arg_val (i := 1) (by decide),
      hb.arg_val (i := 11) (by decide), hi.len_arg, execMul, h.esi, h.edi, h.ebp, h.ebx,
      show (32769 : BitVec 32).toNat = 32769 from rfl, toNat_small32 (show p.len < 2 ^ 32 by omega_using [hv]),
      WSe 0 (by decide), WSe 4 (by decide), WSe 8 (by decide),
      WSe 12 (by decide), WSe 16 (by decide), WSe 20 (by decide),
      WSe 24 (by decide), WSe 28 (by decide),
      WSi 0 (by decide), WSi 4 (by decide), WSi 8 (by decide),
      WSi 12 (by decide), WSi 16 (by decide), WSi 20 (by decide),
      WSi 24 (by decide), WSi 28 (by decide)]
    simp only [writes, stateWords, hs, Nat.reduceMul, Nat.mul_comm 32769]
  · have hfu : Frame [sR o] s.mem u.mem := by
      rw [hm, hs]; exact writes_frame' _ _ 32 (by decide) _ (stateWords_bound p final)
    exact hb.keep ku (by decide) sy (frame_apart hi A.lowS hfu hb.saved)
      (hfu.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨sR o, by simp [changes], fun _ h => h⟩)

theorem results_ok {p : SearchPublic} {o s : State} {final : PrimeSearchResult} (h : SearchDone p o final s) :
    WP isa (.block results) s fun t =>
      (t.gpr .eax = BitVec.ofNat 32 final.status ∧ t.mem = finished p s.mem final) ∧
        Keep [.eax, .ecx, .edx] s t ∧ t.syms = s.syms := by
  have hi := h.input
  have A := hi.abi
  have hb := h.toSearchBase
  have hs : p.stp = arg o 11 := by rw [← hi.2]; rfl
  have hu : p.up = arg o 2 := by rw [← hi.2]; rfl
  have WU (k : Nat) (hk : k < 8) : (arg o 2 + BitVec.ofNat 32 k).setWidth 64 = (arg o 2).setWidth 64 + BitVec.ofNat 64 k :=
    VG.Proof.MlKem.X86.ea_off (by have := A.uBound; omega_using [hk, this])
  have WUi (k : Nat) (hk : k + 4 ≤ 8) : InRegions s.wr ((arg o 2).setWidth 64 + BitVec.ofNat 64 k) 4 :=
    ⟨uR o, by rw [hb.wr, A.wr]; simp, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  rw [show results = (results.take 13) ++ (results.drop 13) from (List.take_append_drop _ _).symm]
  refine WP.block_append (WP.mono (results_head_ok h) fun u ⟨⟨ha, hm, hbu⟩, ku, sy⟩ => ?_)
  have hfu : Frame [sR o] s.mem u.mem := by
    rw [hm, hs]; exact writes_frame' _ _ 32 (by decide) _ (stateWords_bound p final)
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

theorem finished_bytes {p : SearchPublic} {o : State} (h : SearchInput p o) (m : Mem) (r : PrimeSearchResult) :
    Spec.Rsa.bytesAt (finished p m r) (p.op.setWidth 64) p.len = Spec.Rsa.bytesAt m (p.op.setWidth 64) p.len := by
  have A := h.abi
  have hop : p.op = arg o 0 := by rw [← h.2]; rfl
  have hpl : p.len = (arg o 1).toNat := by rw [← h.2]; rfl
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have e := (finished_frame h m r).bytes (R := oR o) (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    exacts [A.os, A.ou]) (by have := A.oBound; change (arg o 1).toNat ≤ _; omega_using [])
    (by change i < (arg o 1).toNat; rw [← hpl]; exact List.mem_range.mp hi)
  rw [hop]; exact e

theorem halves32 {lo : Nat} (hlo : lo < 2 ^ 32) : (0#32 : BitVec 32) ++ BitVec.ofNat 32 lo = BitVec.ofNat 64 lo :=
  zero_half hlo

theorem finished_used {p : SearchPublic} (m : Mem) (r : PrimeSearchResult) (hr : r.used < 2 ^ 32) :
    Spec.Rsa.wordsAt (finished p m r) (p.up.setWidth 64) 1 = [BitVec.ofNat 64 r.used] := by
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
  rw [VG.Proof.Ffdh.X86.KeyInit.readW64_split]
  unfold finished
  have e1 := read_write_eq (writes (writes m (p.stp.setWidth 64) (stateWords p r)) (p.up.setWidth 64)
    [(0, BitVec.ofNat 32 r.used)]) (p.up.setWidth 64) 1 0
  simp only [writes] at e1 ⊢
  rw [show p.up.setWidth 64 + BitVec.ofNat 64 0 + BitVec.ofNat 64 4 = p.up.setWidth 64 + BitVec.ofNat 64 (4 * 1) by
      rw [BitVec.add_zero], e1,
    show p.up.setWidth 64 + BitVec.ofNat 64 0 = p.up.setWidth 64 + BitVec.ofNat 64 (4 * 0) from rfl,
    read_write_ne _ _ (i := 0) (j := 1) (by decide) (by decide) (by decide), read_write_eq,
    show (0 : BitVec 32) = 0#32 from rfl, halves32 hr]

theorem finished_state {p : SearchPublic} {o : State} (h : SearchInput p o) (m : Mem) (r : PrimeSearchResult)
    (h0 : r.remaining < 2 ^ 32) (h1 : p.len < 2 ^ 32) (h2 : 32769 * p.len < 2 ^ 32) (h3 : (requested p.len r) < 2 ^ 32) :
    Spec.Rsa.wordsAt (finished p m r) (p.stp.setWidth 64) 4 = [BitVec.ofNat 64 r.remaining, BitVec.ofNat 64 p.len,
      BitVec.ofNat 64 (32769 * p.len), BitVec.ofNat 64 (requested p.len r)] := by
  have A := h.abi
  have hs : p.stp = arg o 11 := by rw [← h.2]; rfl
  have hu : p.up = arg o 2 := by rw [← h.2]; rfl
  have past (j : Nat) (hj : j < 8) : (finished p m r).readW (p.stp.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 =
      (writes m (p.stp.setWidth 64) (stateWords p r)).readW (p.stp.setWidth 64 + BitVec.ofNat 64 (4 * j)) 32 := by
    unfold finished
    rw [hu]
    refine (writes_frame' _ _ 8 (by decide) _ (usedWords_bound r)).readW (r := sR o) ?_ (fun q hq => ?_) (by decide)
    · rw [hs]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
    · obtain rfl := List.mem_singleton.mp hq; exact A.us.symm
  rw [words_halves, past 0 (by decide), past 1 (by decide), past 2 (by decide), past 3 (by decide),
    past 4 (by decide), past 5 (by decide), past 6 (by decide), past 7 (by decide)]
  simp (disch := decide) only [stateWords, writes, read_write_eq, read_write_ne]
  rw [show (0 : BitVec 32) = 0#32 from rfl, zero_half h0, zero_half h1, zero_half h2, zero_half h3]

/-- The callee-saved registers but `ebx`, from the frame. -/
theorem restore_ok {p : SearchPublic} {o s : State} (hi : SearchInput p o) (hsp : s.gpr .esp = p.S1)
    (hw : below p.sp 16 ∈ s.wr) (hs : Saved s.mem p.S1 o) :
    WP isa (.block Impl.Mont.X86.Compact.restoreRegs) s fun t =>
      (t.gpr .edi = o.gpr .edi ∧ t.gpr .esi = o.gpr .esi ∧ t.gpr .ebp = o.gpr .ebp ∧ t.mem = s.mem) ∧
        Keep [.edi, .esi, .ebp] s t ∧ t.syms = s.syms := by
  have A := hi.abi
  have pe := push_eq hi
  have r (d : Nat) (hd : d + 4 ≤ 16) : InRegions (s.rd ++ s.wr) ((p.S1 + BitVec.ofNat 32 d).setWidth 64) 4 := by
    refine ⟨_, List.mem_append_right _ hw, ?_⟩
    rw [pe]
    have e := addr_sub A (k := 16) (d := d) (by decide) (by omega_using [hd])
    rw [show (p.S1 + BitVec.ofNat 32 d).setWidth 64 = addr (o.gpr .esp - BitVec.ofNat 32 16) d by
      rw [SearchPublic.S1, hi.sp_eq]; rfl, e]
    exact Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])
  obtain ⟨s0, s1, s2, -⟩ := hs
  refine WP.blockKeep _ ?_ (by rfl)
  unfold Impl.Mont.X86.Compact.restoreRegs
  xrun [State.ea, at_, hsp, r 0 (by decide), r 4 (by decide), r 8 (by decide), s0, s1, s2]

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

/-! ## The code never writes `esp` but by its frames -/

theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi =>
  (List.mem_append.mp hi).elim (ha i) (hb i)
theorem noSp_ite {c : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite c a b) := fun i hi =>
  (List.mem_append.mp hi).elim (ha i) (hb i)
theorem noSp_loop {c : Cond} {a : Prog isa} (ha : NoSp a) : NoSp (.loop a c) := ha
theorem noSp_call {n : String} {a : Prog isa} (ha : NoSp a) : NoSp (.call n a) := ha
theorem noSp_alloc {k : Nat} {a : Prog isa} (ha : NoSp a) : NoSp (.frame (.alloc k) a (.free k)) := fun i hi => by
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact ha i hi
  · rfl
theorem noSp_block {is : List Instr} (h : is.all (fun i => !Taint.clobbers i .esp) = true) : NoSp (.block is) :=
  fun i hi => by simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi

theorem body_noSp' (c : Cand) : NoSp (body c.call) := by
  have hz : NoSp zeroOut := noSp_seq (noSp_block (by decide)) (noSp_loop (noSp_block (by decide)))
  have hex : NoSp exhausted := noSp_seq (noSp_block (by decide)) hz
  have hsh : NoSp short := noSp_seq (noSp_block (by decide)) (noSp_ite hex (noSp_block (by decide)))
  have hrej : NoSp reject := noSp_seq (noSp_block (by decide)) (noSp_ite hex (noSp_seq (noSp_block (by decide))
    (noSp_ite (noSp_block (by decide)) (noSp_block (by decide)))))
  have hcl : NoSp classify := noSp_seq (noSp_block (by decide)) (noSp_ite (noSp_block (by decide))
    (noSp_seq (noSp_block (by decide)) (noSp_ite hsh hrej)))
  have hrun : NoSp (candidateRun c.call) := noSp_alloc (noSp_seq (noSp_block (by decide)) (noSp_call c.noSp))
  have hstep : NoSp (candidateStep c.call) :=
    noSp_seq (noSp_block (by decide)) (noSp_ite (noSp_seq hz hsh) (noSp_seq hrun hcl))
  have hit : NoSp (iteration c.call) :=
    noSp_seq (noSp_block (by decide)) (noSp_seq (noSp_ite hex hstep) (noSp_block (by decide)))
  exact noSp_seq (noSp_block (by decide)) (noSp_seq (noSp_loop hit) (noSp_block (by decide)))

theorem consume_zero (r : PrimeSearchResult) : r.consume 0 [] = r := by
  cases r; simp [Spec.Entropy.Result.consume]

theorem search_correct_ok (c : Cand) {s : State} (h : contract.pre s) :
    WP isa (code c.call) s fun t => abiPreserved s t ∧ contract.post s t := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  have A := hp.abi
  have hv := hp.len_valid
  have rl := hp.facts.randLen
  unfold primeEntropy at rl
  have rem := hp.remaining_le
  have h1 : 216 ≤ (s.gpr .esp).toNat := A.stackLow
  have postLocal : ∀ t m (uu : Nat → BitVec 32), abiPreserved s t ∧ contract.post s t →
      Frame [below (s.gpr .esp) (4 * pushRegs.length)] t.mem m →
      abiPreserved s { t with mem := m, unknowns := uu } ∧ contract.post s { t with mem := m, unknowns := uu } := by
    intro t m uu ⟨abi, post⟩ fl
    refine ⟨VG.Proof.Mont.X86.Compact.abi_frame (by omega_using [h1]) abi fl, ?_⟩
    have Ps : Region.Sub ⟨low s + BitVec.ofNat 64 200, 16⟩ (lowR s) := low_sub (by decide)
    rw [show below (s.gpr .esp) (4 * pushRegs.length) = ⟨low s + BitVec.ofNat 64 200, 16⟩ from push_eq hp] at fl
    sig_post [contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at post
    sig_post [contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
    obtain ⟨q1, q2, q3, req, q4, q5⟩ := post
    refine ⟨q1, ?_, ?_, req, ?_, q5⟩
    · rw [VG.Proof.Rsa.rsa_bytes_frame fl ?f1 ?d1]
      · exact q2
      · have := (arg s 1).isLt; omega_using [this]
      · intro r hr; rw [List.mem_singleton.mp hr]; exact (A.lowO.sub_left Ps).symm
    · rw [VG.Proof.Rsa.wordsAt_frame fl ?f2 ?d2]
      · exact q3
      · decide
      · intro r hr; rw [List.mem_singleton.mp hr]; exact (A.lowU.sub_left Ps).symm
    · rw [VG.Proof.Rsa.wordsAt_frame fl ?f3 ?d3]
      · exact q4
      · decide
      · intro r hr; rw [List.mem_singleton.mp hr]; exact (A.lowS.sub_left Ps).symm
  unfold code
  refine WP.frameLocal (rs := pushRegs) (r := .ebx) (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega_using [h1]) (body_noSp' c) postLocal ?_
  refine WP.seq (WP.mono (entry_ok hp) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (search_loop c (final := searchResult s) (tr := []) h1 (consume_zero _).symm)
    fun s2 hd => ?_)
  unfold finish
  refine WP.block_append (WP.mono (results_ok hd) fun s3 ⟨⟨h0, hm3⟩, k3, sy3⟩ => ?_)
  have hfin := finished_frame hp s2.mem (searchResult s)
  rw [← hm3] at hfin
  have Ps : Region.Sub ⟨low s + BitVec.ofNat 64 200, 16⟩ (lowR s) := low_sub (by decide)
  have hb3 : SearchBase p s s3 := hd.toSearchBase.keep k3 (by decide) sy3
    (saved_frame hp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.lowS.sub_left Ps
      · exact A.lowU.sub_left Ps) hfin hd.saved)
    (hfin.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨sR s, by simp [changes], fun _ h => h⟩
      · exact ⟨uR s, by simp [changes], fun _ h => h⟩)
  refine WP.mono (restore_ok hp hb3.sp (by rw [hb3.wr]; exact List.mem_cons_self ..) hb3.saved)
    fun s4 ⟨⟨hdi, hsi, hbp, hm4⟩, k4, sy4⟩ => ?_
  have sp4 : s4.gpr .esp = p.S1 := (k4.gpr (by decide)).trans hb3.sp
  have mem4 : s4.mem = finished p s2.mem (searchResult s) := hm4.trans hm3
  have ax4 : s4.gpr .eax = BitVec.ofNat 32 (searchResult s).status := (k4.gpr (by decide)).trans h0
  have bd := hd.bounds
  have retL : (retR s).Disjoint (lowR s) := Offset.base_disjoint_below _ (by decide)
  change abiPreserved s (popped .ebx 4 s4) ∧ contract.post s (popped .ebx 4 s4)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [popped_four_value, sp4, hm4]; exact hb3.saved.2.2.2
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact hsi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact hdi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact hbp
    · rw [popped_esp, sp4, SearchPublic.S1]
      change p.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 16 = _
      rw [BitVec.sub_add_cancel]; rfl
  · rw [popped_mem, mem4, (finished_frame hp s2.mem _).readW (r := retR s) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [A.retS, A.retU]) (by decide)]
    refine hd.frame.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [A.retO, A.retU, A.retB, A.retS, by rw [← hp.low_eq]; exact retL]
  · sig_post [contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
    rw [ax4, mem4, BitVec.setWidth_append_eq_right]
    have st := (status_lt (searchResult s)).1
    have pe : primeEntropy p.len = 32769 * p.len := rfl
    refine ⟨toNat_small32 (by omega_using [st]), ?_, finished_used _ _ (by omega_using [hv, rl, bd]), _, ?_,
      Search.search_requests _ _ _ _ _⟩
    · exact (finished_bytes hp _ _).trans hd.output
    · exact finished_state hp _ _ (by omega_using [rem, bd]) (by omega_using [hv]) (by omega_using [hv]) (by omega_using [hv, bd, pe])

theorem correct (c : Cand) (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa (code c.call) s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := search_correct_ok c h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.X86.Search

end

end

-- separate module: the search's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # The search in constant time (i686)

Two runs whose public data agree have the same arguments, `e`, counted
candidates and trace (`pub_same`), so they start at the same loop point. The
entry loads the state's pointer from the stack, then reads through it
(`entry_ct`); an iteration branches alike in both runs and leaves them at
the same next point, from the trace (`ct_step`), so the loop leaks the
points alone (`loop_ct`), the octets consumed its measure; `finish` stores
through the state's and `used`'s pointers, which it loads from the stack
(`finish_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)

/-! ## The loop -/

/-- What an iteration from the point `q` leaves. -/
def CTNext (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  (pubCont p T q ∧ isa.eval .e t = some true ∧ LiveCT p T (nextPt p T q) t) ∨
    (¬pubCont p T q ∧ isa.eval .e t = some false)

theorem entryOf_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : entryOf p o q.1 = (nextLeak T q.2.2).length :: nextLeak T q.2.2 := by
  rw [leak_of hT hfin hk]

theorem ct_step (c : Cand) (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : LiveCT p T q s) :
    WP isa (iteration c.call) s (CTNext p T q) := by
  obtain ⟨o, hT, L, hf⟩ := h
  have ci := cont_iff L.input hT hf
  refine WP.mono (iteration_ok c L hf) fun t ht => ?_
  unfold IterPost at ht
  split at ht
  · rename_i hc
    have hk := hc.1
    have e : nextPt p T q = (q.1 + candUsed p o q.1, nextK p o q.1 q.2.1, q.2.2 ++ entryOf p o q.1) := by
      unfold nextPt nextK
      rw [← used_eq L.input hT hf hk, ← status_eq hT hf hk, entryOf_eq hT hf hk]
    refine .inl ⟨ci.mp hc, ht.1, ?_⟩
    rw [e]
    exact ⟨o, hT, ht.2.1, ht.2.2⟩
  · rename_i hc
    exact .inr ⟨fun h => hc (ci.mpr h), ht.1⟩

/-- Two loop states at the same point, `n` octets of the tape left. -/
def LoopPair (p : SearchPublic) (T : List Nat) (n : Nat) (s t : State) : Prop :=
  ∃ q : Pt, n = p.randLen - q.1 ∧ LiveCT p T q s ∧ LiveCT p T q t

theorem iteration_pair (c : Cand) (p : SearchPublic) (T : List Nat) (n : Nat) :
    RelCT isa (LoopPair p T n) (iteration c.call) fun s t =>
      isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
      (isa.eval .e s = some true → ∃ m < n, LoopPair p T m s t) := by
  have hc := two_post (Φ := fun (q : Pt) s => n = p.randLen - q.1 ∧ LiveCT p T q s)
    (Ψ := fun q t => n = p.randLen - q.1 ∧ CTNext p T q t) ((iteration_ct c p T).mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) fun _ _ h => h) fun q s h =>
      WP.mono (ct_step c p T q s h.2) fun _ ht => ⟨h.1, ht⟩
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨co, e₁, L₁⟩ | ⟨nc, e₁⟩
  · rcases h₂ with ⟨_, e₂, L₂⟩ | ⟨nc, _⟩
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨p.randLen - (nextPt p T q).1, ?_, _, rfl, L₁, L₂⟩⟩
      obtain ⟨_, _, L, _⟩ := L₁
      have hle := L.used_le
      have h0 := co.2.2.2
      simp only [nextPt] at hle ⊢
      omega_using [hn, hle, h0]
    · exact absurd co nc
  · rcases h₂ with ⟨co, _, _⟩ | ⟨_, e₂⟩
    · exact absurd co nc
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun ht => ?_⟩
      rw [e₁] at ht
      cases ht

theorem loop_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (LiveCT p T)) (.loop (iteration c.call) .e) fun _ _ => True := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .e) (Q := fun _ _ => True) (LoopPair p T)
    (iteration_pair c p T) (p.randLen - q.1) _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-! ## The entry and the results -/

/-- An entry state, with the public data `p` and the trace `T`, after the push. -/
def EntryAt (p : SearchPublic) (T : List Nat) (_ : Unit) (s : State) : Prop :=
  ∃ o, SearchInput p o ∧ (searchResult o).trace = T ∧ s = pushed pushRegs o

/-- `mov eax, [state]`. -/
theorem stLoad_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa (.block [.mov .eax (.mem (param 0 11))]) s fun t => t.gpr .eax = p.stp ∧ t.gpr .esp = p.S1 := by
  have hst : p.stp = arg o 11 := by rw [← hb.input.2]; rfl
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 11) (d := 64) rfl, hb.arg_in (i := 11) (by decide),
    hb.arg_val (i := 11) (by decide), hst]
  exact hb.sp

theorem entry_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (EntryAt p T)) (.block entry) (Two (LiveCT p T)) := by
  refine (two_post (Ψ := fun _ s => LiveCT p T (0, p.remaining, []) s) ?_ fun _ s ⟨o, hi, hT, e⟩ => ?_).mono
    (fun _ _ h => h) fun _ _ ⟨_, h₁, h₂⟩ => ⟨_, h₁, h₂⟩
  · rw [show entry = [.mov .eax (.mem (param 0 11))] ++ entry.drop 1 from rfl]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (_ : Unit) t => t.gpr .eax = p.stp ∧ t.gpr .esp = p.S1)
      [.esp] (fun _ s₁ s₂ ⟨o₁, i₁, _, e₁⟩ ⟨o₂, i₂, _, e₂⟩ r hr => by
        obtain rfl := List.mem_singleton.mp hr
        subst e₁ e₂
        exact (push_base i₁).sp.trans (push_base i₂).sp.symm) (by taint_decide)
      fun _ s ⟨o, hi, _, e⟩ => by subst e; exact stLoad_ok (push_base hi))
      (two_taint [.eax, .esp] (fun _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide)))
  · subst e
    have L := entry_ok hi
    obtain ⟨_, rfl⟩ := hi
    exact WP.mono L fun t L => ⟨o, hT, L, (consume_zero _).symm⟩

/-- A finished search with the public data `p`. -/
def DoneAt (p : SearchPublic) (_ : Unit) (s : State) : Prop := ∃ o r, SearchDone p o r s

/-- The results' head: `out_len`'s budget, and the state's pointer in `edx`. -/
theorem finHead_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa (.block (results.take 4)) s fun t => t.gpr .edx = p.stp ∧ t.gpr .esp = p.S1 := by
  have hi := hb.input
  have hv := hi.len_valid
  have hs : p.stp = arg o 11 := by rw [← hi.2]; rfl
  simp only [results, List.take, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 1) (d := 24) rfl, hb.arg_ea (i := 11) (d := 64) rfl,
    hb.arg_in (i := 1) (by decide), hb.arg_in (i := 11) (by decide), hb.arg_val (i := 1) (by decide),
    hb.arg_val (i := 11) (by decide), execMul, hs]
  exact hb.sp

/-- After `used`'s pointer is loaded. -/
def FinB (p : SearchPublic) (v : State) : Prop := v.gpr .edx = p.up ∧ v.gpr .esp = p.S1

/-- After the state's words. -/
def FinA (p : SearchPublic) (u : State) : Prop :=
  u.gpr .esp = p.S1 ∧ WP isa (.block ((results.drop 13).take 1)) u (FinB p)

/-- With the state's pointer in `edx`. -/
def FinH (p : SearchPublic) (t : State) : Prop :=
  t.gpr .edx = p.stp ∧ t.gpr .esp = p.S1 ∧ WP isa (.block ((results.take 13).drop 4)) t (FinA p)

theorem finish_ct (p : SearchPublic) : RelCT isa (Two (DoneAt p)) (.block finish) fun _ _ => True := by
  rw [show finish = results.take 4 ++ ((results.take 13).drop 4 ++ ((results.drop 13).take 1 ++
    (results.drop 14 ++ Impl.Mont.X86.Compact.restoreRegs))) from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun _ => FinH p) [.esp]
    (fun _ s₁ s₂ ⟨_, _, D₁⟩ ⟨_, _, D₂⟩ r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact D₁.sp.trans D₂.sp.symm) (by taint_decide)
    fun _ s ⟨o, r, D⟩ => ?_) ?_)
  · have hb := D.toSearchBase
    have H := results_head_ok D
    rw [show results.take 13 = results.take 4 ++ (results.take 13).drop 4 from rfl, WP.block_append_iff] at H
    exact WP.mono (WP.block_and H (finHead_ok hb)) fun t ⟨ht, he, hs⟩ => ⟨he, hs, WP.mono ht
      fun u ⟨⟨_, _, hbu⟩, ku, _⟩ => ⟨(ku.gpr (by decide)).trans hb.sp,
        WP.mono (WP.blockKeep [.edx] (upLoad_ok hbu) (by rfl)) fun v ⟨⟨he', _⟩, kv, _⟩ =>
          ⟨he', (kv.gpr (by decide)).trans hbu.sp⟩⟩⟩
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun _ => FinA p) [.edx, .esp]
    (fun _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm]) (by taint_decide) fun _ _ h => h.2.2) ?_)
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun _ => FinB p) [.esp]
    (fun _ s₁ s₂ h₁ h₂ r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact h₁.1.trans h₂.1.symm) (by taint_decide) fun _ _ h => h.2) ?_)
  exact two_taint [.edx, .esp] (fun _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

/-! ## The search -/

/-- An entry state with the public data and trace `pt`. -/
def EntCT (pt : SearchPublic × List Nat) (o : State) : Prop := SearchInput pt.1 o ∧ (searchResult o).trace = pt.2

theorem body_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (EntryAt p T)) (body c.call) fun _ _ => True := by
  unfold body
  exact RelCT.seq (entry_ct p T) (RelCT.seq (two_post (Ψ := fun _ s => DoneAt p () s) (loop_ct c p T)
    fun q s ⟨o, hT, L, hf⟩ => WP.mono (search_loop c L hf) fun t D => ⟨o, _, D⟩)
    (two_map (fun _ => ()) (fun _ _ h => h) (finish_ct p)))

theorem code_ct (c : Cand) : RelCT isa (Two EntCT) (code c.call) fun _ _ => True := by
  unfold code
  refine RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ ⟨pt, h₁, h₂⟩ => h₁.1.sp_eq.symm.trans h₂.1.sp_eq) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨pt, h₁, h₂⟩, e₁, e₂⟩ x₁ x₂
  exact body_ct c pt.1 pt.2 _ _ _ _ _ _ ⟨(), ⟨s₁, h₁.1, h₁.2, e₁⟩, ⟨s₂, h₂.1, h₂.2, e₂⟩⟩ x₁ x₂

theorem wordsAt4 (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 4 =
    [m.readW (p + BitVec.ofNat 64 0) 64, m.readW (p + BitVec.ofNat 64 8) 64, m.readW (p + BitVec.ofNat 64 16) 64,
      m.readW (p + BitVec.ofNat 64 24) 64] := rfl

/-- Two entry states whose public data agree have the same public data and trace. -/
theorem pub_same {s t : State} (H : contract.pub s t) :
    searchOfState s = searchOfState t ∧ (searchResult s).trace = (searchResult t).trace := by
  sig_pub [contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  obtain ⟨SP, sy, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, a4])
  obtain ⟨L₃, -⟩ := List.append_inj L₁ (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, a4])
  obtain ⟨L₄, L₅⟩ := List.append_inj L₃ (by simp [Spec.Rsa.bytesAt, a4])
  have D := inj L₄
  rw [wordsAt4, wordsAt4] at L₅
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at L₅
  obtain ⟨k, _, _, _⟩ := L₅
  rw [BitVec.add_zero, BitVec.add_zero] at k
  refine ⟨?_, L₂⟩
  simp only [searchOfState, SearchPublic.mk.injEq]
  exact ⟨a0, a2, a3, a5, a7, a9, a11, SP, congrArg BitVec.toNat a1, congrArg BitVec.toNat a4,
    congrArg BitVec.toNat a6, congrArg BitVec.toNat a8, congrArg BitVec.toNat a10, k, D, sy⟩

theorem constantTime (c : Cand) : ConstantTime isa contract.pre contract.pub (code c.call) := by
  intro s t tr ur sf tf S T H E F
  have P := pub_same H
  exact (code_ct c _ _ _ _ _ _ ⟨(searchOfState s, (searchResult s).trace), ⟨⟨S, rfl⟩, rfl⟩,
    ⟨⟨T, P.1.symm⟩, P.2.symm⟩⟩ E F).1

end VG.Proof.RsaKeyGen.X86.Search
