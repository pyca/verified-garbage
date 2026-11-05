module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Leaf
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Leaf
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86.Common

-- separate module: the search's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # How the search ends (i686)

The terminal states (`exhausted_ok`, `accept_ok`), and the request for more
of the tape (`request_ok`, `short_ok`), whose larger and smaller values are
chosen by masks of the borrows (`select_mask`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit primeRequest)

/-- Writes to `out` keep the frame and what the search may write. -/
theorem out_changes {o : State} {m m' : Mem} (h : Frame [oR o] m m') : Frame (changes o) m m' :=
  h.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨oR o, by simp [changes], fun _ h => h⟩

theorem frame_apart {p : SearchPublic} {o : State} (h : SearchInput p o) {r : Region}
    (hd : (lowR o).Disjoint r) {m m' : Mem} (hf : Frame [r] m m') (hs : Saved m p.S1 o) : Saved m' p.S1 o := by
  have A := h.abi
  have hS : p.S1 = o.gpr .esp - BitVec.ofNat 32 16 := by rw [SearchPublic.S1, h.sp_eq]
  have sub : Region.Sub (below (o.gpr .esp) 16) (lowR o) := by
    rw [h.low_eq]; exact below_sub (by decide) A.stackLow
  have wd (k : Nat) (hk : k < 4) : (below (o.gpr .esp) 16).Contains ((p.S1 + BitVec.ofNat 32 (4 * k)).setWidth 64) 4 := by
    rw [hS]
    have e : (o.gpr .esp - BitVec.ofNat 32 16 + BitVec.ofNat 32 (4 * k)).setWidth 64 =
        (o.gpr .esp - BitVec.ofNat 32 16).setWidth 64 + BitVec.ofNat 64 (4 * k) :=
      VG.Proof.MlKem.X86.ea_off (by rw [sub_toNat (by have := A.stackLow; simp only [stack] at this; omega)]; have := A.stackBound; omega)
    rw [e]; exact Offset.contains_base _ (by omega) (by omega)
  have keep (k : Nat) (hk : k < 4) := hf.readW (w := 32) (wd k hk) (fun r' hr' => by
    obtain rfl := List.mem_singleton.mp hr'; exact fun x h₁ h₂ => hd x (sub x h₁) h₂) (by decide)
  obtain ⟨h0, h1, h2, h3⟩ := hs
  exact ⟨(keep 0 (by decide)).trans h0, (keep 1 (by decide)).trans h1, (keep 2 (by decide)).trans h2,
    (keep 3 (by decide)).trans h3⟩

theorem terminal_ok (s : State) (status : Nat) :
    WP isa (.block (terminal status)) s fun t =>
      (t.gpr .edi = 0 ∧ t.gpr .ebp = 0 ∧ t.gpr .ebx = BitVec.ofNat 32 status ∧ t.mem = s.mem) ∧
        Keep [.edi, .ebp, .ebx] s t ∧ t.syms = s.syms := by
  refine WP.blockKeep _ ?_ (by rfl)
  unfold terminal
  xrun

/-- Exhausted: zeros at `out`, after `used` octets. -/
theorem exhausted_ok {p : SearchPublic} {o s : State} {used : Nat} (h : SearchBase p o s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 used) (hu : used ≤ p.randLen) (tr : List Nat) :
    WP isa exhausted s (SearchDone p o ⟨.exhausted, used, tr⟩) := by
  unfold exhausted
  refine WP.seq (WP.mono (terminal_ok s 3) fun u ⟨⟨h9, h10, h11, hm⟩, k, sy⟩ => ?_)
  have hb := h.step k (by decide) sy hm
  refine WP.mono (zeroOut_ok hb) fun t ⟨⟨hf, hz⟩, kt, syt⟩ => ?_
  have A := h.input.abi
  exact ⟨hb.keep kt (by decide) syt (frame_apart h.input A.lowO hf hb.saved) (out_changes hf),
    (kt.gpr (by decide)).trans ((k.gpr (by decide)).trans hsi), (kt.gpr (by decide)).trans h9,
    (kt.gpr (by decide)).trans h10, (kt.gpr (by decide)).trans h11, hz, hu, Nat.zero_le _, Nat.zero_le _⟩

theorem add_ofNat32 (a b : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- The prime, after `used + n` octets. -/
theorem accept_ok {p : SearchPublic} {o s : State} {used n c : Nat} (h : SearchBase p o s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 used) (hc : s.gpr .ecx = BitVec.ofNat 32 n) (hu : used + n ≤ p.randLen)
    (hout : Spec.Rsa.bytesAt s.mem (p.op.setWidth 64) p.len = Spec.Rsa.i2osp c p.len) (tr : List Nat) :
    WP isa (.block accept) s (SearchDone p o ⟨.accepted c, used + n, tr⟩) := by
  refine WP.mono (WP.blockKeep [.esi, .edi, .ebp, .ebx] (Q := fun t => t.gpr .esi = BitVec.ofNat 32 (used + n) ∧
    t.gpr .edi = 0 ∧ t.gpr .ebp = 0 ∧ t.gpr .ebx = 1 ∧ t.mem = s.mem) ?_ (by rfl))
    fun t ⟨⟨h8', h9, h10, h11, hm⟩, k, sy⟩ => ⟨h.step k (by decide) sy hm, h8', h9, h10, h11,
      by rw [hm]; exact hout, hu, Nat.zero_le _, Nat.zero_le _⟩
  unfold accept terminal
  xrun [hsi, hc, add_ofNat32]

/-! ## Asking for more -/

theorem toNat_small32 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `a`, or `b` where the borrow `c` is set: the mask of `sbb r, r`. -/
theorem select_mask (a b : BitVec 32) (c : Bool) :
    a ^^^ ((b ^^^ a) &&& (0#32 - BitVec.setWidth 32 (BitVec.ofBool c))) = if c then b else a := by
  cases c
  · simp only [Bool.false_eq_true, ite_false]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool false)) = 0#32 from rfl, BitVec.and_zero, BitVec.xor_zero]
  · simp only [ite_true]
    rw [show (0#32 - BitVec.setWidth 32 (BitVec.ofBool true)) = BitVec.allOnes 32 from rfl, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem double32 (a : Nat) : BitVec.ofNat 32 a + BitVec.ofNat 32 a = BitVec.ofNat 32 (2 * a) := by
  rw [add_ofNat32, Nat.two_mul]

/-- The next tape's length, from `left` octets of the tape and the budget in
`ebp`. -/
theorem request_ok {p : SearchPublic} {o s : State} {left : Nat} (h : SearchBase p o s)
    (hleft : left ≤ 32769 * p.len)
    (hax : s.gpr .eax = BitVec.ofNat 32 left) (hbp : s.gpr .ebp = BitVec.ofNat 32 (32769 * p.len)) :
    WP isa (.block request) s fun t =>
      (t.gpr .ebp = BitVec.ofNat 32 (primeRequest p.len left) ∧ t.gpr .ebx = 0 ∧ t.mem = s.mem) ∧
        Keep [.eax, .ecx, .edx, .ebp, .ebx] s t ∧ t.syms = s.syms := by
  have hv := h.input.len_valid
  have hL : arg o 1 = BitVec.ofNat 32 p.len := by
    rw [← h.input.2]; change arg o 1 = BitVec.ofNat 32 (arg o 1).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.blockKeep _ ?_ (by rfl)
  simp only [request, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, h.arg_ea (i := 1) (d := 24) rfl, h.arg_in (i := 1) (by decide),
    h.arg_val (i := 1) (by decide), hL, hax, hbp, double32, select_mask]
  have e16 : 2 * (2 * (2 * (2 * p.len))) = 16 * p.len := by omega
  rw [e16, toNat_small32 (show left < 2 ^ 32 by omega), toNat_small32 (show 16 * p.len < 2 ^ 32 by omega),
    toNat_small32 (show 32769 * p.len < 2 ^ 32 by omega)]
  have hm : (if decide (left < 16 * p.len) = true then BitVec.ofNat 32 (16 * p.len) else BitVec.ofNat 32 left) =
      BitVec.ofNat 32 (max left (16 * p.len)) := by
    by_cases hl : left < 16 * p.len
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hl))]; congr 1; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hl))]; congr 1; omega
  rw [hm, double32, toNat_small32 (show 2 * max left (16 * p.len) < 2 ^ 32 by omega)]
  unfold primeRequest Spec.Entropy.request primeEntropy
  by_cases hc : 32769 * p.len < 2 * max left (16 * p.len)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (decide_eq_true hc))]; congr 1; omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hc))]; congr 1; omega

theorem sub_eq_beq {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 c == 0) = decide (a = c) := by
  by_cases e : a = c
  · subst e; rw [BitVec.sub_self, decide_eq_true rfl]; rfl
  · rw [decide_eq_false e]
    refine beq_eq_false_iff_ne.mpr fun h => e ?_
    have h'' : BitVec.ofNat 32 a = BitVec.ofNat 32 c := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 32 a) (BitVec.ofNat 32 c), h]
      exact BitVec.zero_add _
    have := congrArg BitVec.toNat h''
    rwa [toNat_small32 ha, toNat_small32 hc] at this

theorem SearchInput.len_arg {p : SearchPublic} {o : State} (h : SearchInput p o) :
    arg o 1 = BitVec.ofNat 32 p.len := by
  rw [← h.2]; change arg o 1 = BitVec.ofNat 32 (arg o 1).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem SearchInput.randLen_arg {p : SearchPublic} {o : State} (h : SearchInput p o) :
    arg o 8 = BitVec.ofNat 32 p.randLen := by
  rw [← h.2]; change arg o 8 = BitVec.ofNat 32 (arg o 8).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The tape ended inside a candidate, after `used` octets, with `k`
counted candidates left: exhausted if it had the whole budget, else a
request for more. -/
theorem short_ok {p : SearchPublic} {o s : State} {used k : Nat} (h : SearchBase p o s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 used) (hdi : s.gpr .edi = BitVec.ofNat 32 k) (hu : used ≤ p.randLen)
    (hk : k ≤ p.remaining)
    (hout : Spec.Rsa.bytesAt s.mem (p.op.setWidth 64) p.len = List.replicate p.len 0) (tr : List Nat) :
    WP isa short s (SearchDone p o (if primeEntropy p.len ≤ p.randLen - used then ⟨.exhausted, used, tr⟩
      else ⟨.entropy k (primeRequest p.len (p.randLen - used)), used, tr⟩)) := by
  have hi := h.input
  have f := hi.facts
  have hv := hi.len_valid
  have rl := f.randLen
  unfold primeEntropy at rl
  unfold short
  refine WP.seq (WP.mono (WP.blockKeep [.eax, .ecx, .edx, .ebp]
    (Q := fun t => t.gpr .eax = BitVec.ofNat 32 (p.randLen - used) ∧ t.gpr .ebp = BitVec.ofNat 32 (32769 * p.len) ∧
      t.zf = some (decide (p.randLen - used = 32769 * p.len)) ∧ t.mem = s.mem) ?_ (by rfl))
    fun u ⟨⟨h0, h1, he, hm⟩, k', sy⟩ => ?_)
  · simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, h.arg_ea (i := 1) (d := 24) rfl, h.arg_ea (i := 8) (d := 52) rfl,
      h.arg_in (i := 1) (by decide), h.arg_in (i := 8) (by decide), h.arg_val (i := 1) (by decide),
      h.arg_val (i := 8) (by decide), hi.len_arg, hi.randLen_arg, hsi, execMul,
      show (32769 : BitVec 32).toNat = 32769 from rfl, toNat_small32 (show p.len < 2 ^ 32 by omega),
      BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega) hu]
    rw [sub_eq_beq (by omega) (by omega), Nat.mul_comm]
  have hu' := h.step k' (by decide) sy hm
  have hsi' : u.gpr .esi = BitVec.ofNat 32 used := (k'.gpr (by decide)).trans hsi
  refine WP.ite _ he (fun hz => ?_) (fun hz => ?_)
  · have hz := of_decide_eq_true hz
    rw [ite_eq_left_of_eq_true _ _ (by unfold primeEntropy; exact eq_true (by omega))]
    exact exhausted_ok hu' hsi' hu tr
  · have hz := of_decide_eq_false hz
    rw [ite_eq_right_of_eq_false _ _ (by unfold primeEntropy; exact eq_false (by omega))]
    refine WP.mono (request_ok hu' (by omega) h0 h1)
      fun t ⟨⟨h10, h11, hmt⟩, kt, syt⟩ => ⟨hu'.step kt (by decide) syt hmt, (kt.gpr (by decide)).trans hsi',
        (kt.gpr (by decide)).trans ((k'.gpr (by decide)).trans hdi), h10, h11,
        by rw [hmt, hm]; exact hout, hu, hk, by
          unfold primeRequest Spec.Entropy.request; exact Nat.min_le_right _ _⟩

end VG.Proof.RsaKeyGen.X86.Search
