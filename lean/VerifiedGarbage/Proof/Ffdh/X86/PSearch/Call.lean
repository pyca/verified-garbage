module

public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.CallPre
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Verified
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Entry
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # The attempt's call (x86)

`vg_ffdh_parameter_candidate_sieved`, called with its arguments in the
frame, returns the status of the candidate at the tape's offset, writes its
output and the octets it consumed (to the state's word at 80), changing
memory only at the output, that word, the working space and the stack the
controller uses (`call_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd bytes_frame)
open VG.Proof.Dsa.X86 (argumentPointer)

theorem callee_stack : stackUse Impl.Ffdh.X86.Candidate.code = 172 := by rsa_stack_use

theorem callee_noSp : NoSp Impl.Ffdh.X86.Candidate.code := NoSp.of_all (by rsa_stack_shape)

/-- The bytes `[u, u + l)` of `n` at `p`. -/
theorem bytes_window (m : Mem) (p : Addr) {u l n : Nat} (h : u + l ≤ n) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 u) l = ((Spec.Rsa.bytesAt m p n).drop u).take l := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt]; omega_arith)
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The candidate at the tape's offset `used`. -/
abbrev candOf (o : State) (used : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  candAt (ofState o).bits (ofState o).gen (ofState o).rand used

/-- What an attempt leaves at the output. -/
def AttemptOut (o : State) (used : Nat) (m : Mem) : Prop :=
  Spec.Rsa.bytesAt m (argumentPointer o 0) (arg o 1).toNat =
    match candOf o used with
    | some (some q, _) => Spec.Rsa.i2osp q (arg o 1).toNat
    | _ => List.replicate (arg o 1).toNat 0

/-- Words of the state, through writes apart from each of them. -/
theorem ctl_frameW {m m' : Mem} {S : BitVec 32} {ds : List Nat} {f : Nat → BitVec 32} (h : Ctl m S ds f)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ d ∈ ds, ∀ r ∈ rs, (⟨addr S d, 4⟩ : Region).Disjoint r) :
    Ctl m' S ds f := fun d hd' => by
  rw [hf.readW (Region.contains_self _ _) (hd d hd') (by decide)]; exact h d hd'

theorem call_covers {o t : State} {used : Nat} (A : PSearchABI o) (hu : used < (arg o 6).toNat)
    (hrd : t.rd = o.rd) (hwr : t.wr = frR o :: o.wr) :
    Covers (callRd o used ++ callWr o) (t.rd ++ t.wr) ∧ Covers (callWr o) t.wr := by
  have hw : ∀ r ∈ callWr o, ∃ r' ∈ t.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := by
    intro r hr
    rw [hwr, A.wr]
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨oR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨sR o, by simp, 80, cu_base A, show 80 + 8 ≤ 128 by decide⟩
    · exact ⟨bR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨frR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  have hT : o.rd = [rR o, tR o] := by
    have hp := A.rdPrefix
    have hd := A.rdTable
    rw [← List.take_append_drop (o.rd.length - 1) o.rd, hp, hd]
    show [rR o] ++ tableRs o = _
    rw [tableRs_eq]; rfl
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [hrd, hT]
    rw [callRd, tableRs_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨rR o, by simp, used, win_base A hu, show used + ((arg o 6).toNat - used) ≤ (arg o 6).toNat by omega_arith⟩
    · exact ⟨tR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', off, hb⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', off, hb⟩

/-- A region apart from every region the run may write. -/
theorem apart {o : State} (A : PSearchABI o) {R : Region} (ho : R.Disjoint (oR o)) (hu : R.Disjoint (uR o))
    (hb : R.Disjoint (bR o)) (hs : R.Disjoint (sR o)) (ha : R.Disjoint (aR o)) (hl : R.Disjoint (lowR o)) :
    ∀ r ∈ frameR o, R.Disjoint r := by
  intro r hr
  rw [frameR, A.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ho, hu, hb, hs, ha, hl]

/-- The tape, through the run's writes. -/
theorem rand_apart {o : State} (A : PSearchABI o) : ∀ r ∈ frameR o, (rR o).Disjoint r :=
  apart A A.or_.symm A.ur.symm A.rb A.rs A.ra A.lowRand.symm

/-- The call's return address. -/
theorem ret_eq {o t : State} (A : PSearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    (t.gpr .esp - 4).setWidth 64 = low o + BitVec.ofNat 64 172 := by
  rw [esp_sub4 A he, sw_sub A (by decide)]

/-- The stack below the call. -/
theorem below_eq {o t : State} (A : PSearchABI o) (he : t.gpr .esp = o.gpr .esp - BitVec.ofNat 32 argsBytes) :
    below (t.gpr .esp) (stackUse Impl.Ffdh.X86.Candidate.code + 4) = ⟨low o, 176⟩ := by
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hl := low_toNat A
  have := (o.gpr .esp).isLt
  have e : (o.gpr .esp - BitVec.ofNat 32 argsBytes - BitVec.ofNat 32 (172 + 4)).setWidth 64 = low o := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, hl, argsBytes]
    omega_arith
  rw [callee_stack, below, he, e]

theorem rand_length {o : State} : (ofState o).rand.length = (arg o 6).toNat := by
  simp only [ofState, Spec.Rsa.bytesAt, List.length_map, List.length_range]

/-- The callee's tape, on its entry. -/
theorem entry_bytes {o t : State} {ds : List Nat} {f : Nat → BitVec 32} {used : Nat} (h : Fr o ds f t)
    (hu : used < (arg o 6).toNat) (v : BitVec 32) :
    Spec.Rsa.bytesAt (t.mem.writeW (low o + BitVec.ofNat 64 172) v) ((arg o 5 + BitVec.ofNat 32 used).setWidth 64)
      ((arg o 6).toNat - used) = (ofState o).rand.drop used := by
  have A := h.abi
  have hrb := A.rBound
  have Rs : Region.Sub ⟨low o + BitVec.ofNat 64 172, 4⟩ (lowR o) := low_sub (by decide)
  have W := win_sub A hu
  have fe : Frame [⟨low o + BitVec.ofNat 64 172, 4⟩] t.mem (t.mem.writeW (low o + BitVec.ofNat 64 172) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [bytes_frame fe (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ((A.lowRand.sub_left Rs).sub_right W).symm)
      (by omega_arith), bytes_frame h.frame (fun r hr => (rand_apart A r hr).sub_left W) (by omega_arith),
    win_base A hu, bytes_window _ _ (show used + ((arg o 6).toNat - used) ≤ (arg o 6).toNat by omega_arith)]
  show _ = (Spec.Rsa.bytesAt o.mem (argumentPointer o 5) (arg o 6).toNat).drop used
  rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt])]

theorem candidateStatus_le (c : Option (Option Nat × Spec.RsaKeyGen.Rand)) : candidateStatus c ≤ 2 := by
  unfold candidateStatus; split <;> decide

/-- The state's word at `d < 80`, apart from the candidate's `used`. -/
theorem word_cu {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 80) :
    (⟨addr (arg o 9) d, 4⟩ : Region).Disjoint (cuR o) := by
  rw [cuR, cu_base A, Spill.addr_eq_of A.sBound (d := d) (by omega_arith)]
  exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The state's word at `d` lies in the state's region. -/
theorem word_sub {o : State} (A : PSearchABI o) {d : Nat} (hd : d + 4 ≤ 128) :
    Region.Sub ⟨addr (arg o 9) d, 4⟩ (sR o) := by
  rw [Spill.addr_eq_of A.sBound hd]; exact Offset.sub_base _ hd

theorem call_ok {o t : State} {e : BitVec 32} {used n : Nat}
    (h : Fr o liveDs (liveF (ofState o) e used n) t) (hu : used < (arg o 6).toNat) (ha : ArgsAt o used 9 t.mem) :
    WP isa (.call Spec.Ffdh.sievedParameterCandidateApi.name Impl.Ffdh.X86.Candidate.code) t fun u =>
      Fr o liveDs (liveF (ofState o) e used n) u ∧
      u.gpr .eax = BitVec.ofNat 32 (candidateStatus (candOf o used)) ∧ AttemptOut o used u.mem ∧
      u.mem.readW (addr (arg o 9) candOff) 32 =
        BitVec.ofNat 32 (candUsed (ofState o).bits (ofState o).gen (ofState o).rand used) := by
  have A := h.abi
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  have hb := A.stackBound
  have hn : (t.gpr .esp).toNat = (o.gpr .esp).toNat - 36 := by
    rw [h.esp]; exact VG.X86.sub_toNat (by unfold argsBytes; omega_arith)
  obtain ⟨hc, hcw⟩ := call_covers (t := t) A hu h.rd h.wr
  refine WP.of_syms (WP.call Cand.verified.1 callee_noSp (by rw [callee_stack, hn]; omega_arith)
    (call_pre A hu h.esp ha h.syms h.frame) hc hcw fun u hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ sy => ?_)
  have hp := hpost
  sig_post [Cand.contract, Spec.Ffdh.sievedParameterCandidateContract, Spec.Ffdh.parameterCandidateSig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at hp
  simp only [ce_arg A h.esp ha _ _ (show 0 < 9 by decide), ce_arg A h.esp ha _ _ (show 1 < 9 by decide),
    ce_arg A h.esp ha _ _ (show 2 < 9 by decide), ce_arg A h.esp ha _ _ (show 3 < 9 by decide),
    ce_arg A h.esp ha _ _ (show 4 < 9 by decide), ce_arg A h.esp ha _ _ (show 5 < 9 by decide),
    ce_arg A h.esp ha _ _ (show 6 < 9 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte, ret_eq A h.esp] at hp
  have hlen : (BitVec.ofNat 32 ((arg o 6).toNat - used)).toNat = (arg o 6).toNat - used := by
    have := (arg o 6).isLt; rw [BitVec.toNat_ofNat]; omega_arith
  rw [hlen, show low o + 172#64 = low o + BitVec.ofNat 64 172 from rfl, entry_bytes h hu] at hp
  obtain ⟨hr, hout, hw⟩ := hp
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  have hS := A.sBound
  have hA : Aligned liveDs := by decide
  have Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  have Bs : Region.Sub ⟨low o, 176⟩ (lowR o) := Region.sub_prefix (by decide)
  have fr : Frame (frameR o) t.mem u.mem := hf.sub fun r hr => by
    rw [below_eq A h.esp] at hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨oR o, List.mem_append_left _ (oR_mem A), fun _ h => h⟩
    · exact ⟨sR o, List.mem_append_left _ (sR_mem A), cu_sub A⟩
    · exact ⟨bR o, List.mem_append_left _ (bR_mem A), fun _ h => h⟩
    · exact ⟨lowR o, List.mem_append_right _ (List.mem_singleton_self _), Fs⟩
    · exact ⟨lowR o, List.mem_append_right _ (List.mem_singleton_self _), Bs⟩
  refine ⟨⟨A, hrd.trans h.rd, hwr.trans h.wr, sy.trans h.syms, by rw [hcs .esp (by decide), h.esp],
    by rw [hcs .esi (by decide), h.esi], fun r hr hne hsp => by rw [hcs r hr, h.saved r hr hne hsp],
    h.frame.trans fr, ctl_frameW h.words hf fun d hd r hr => ?_⟩, ?_, ?_, ?_⟩
  · have hd4 : d + 4 ≤ 76 := by
      simp only [liveDs, List.mem_cons, List.not_mem_nil, or_false] at hd; omega_arith
    have ws := word_sub A (d := d) (by omega_arith)
    rw [below_eq A h.esp] at hr
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact A.os.symm.sub_left ws
    · exact word_cu A (by omega_arith)
    · exact A.bs.symm.sub_left ws
    · exact (A.lowS.symm.sub_left ws).sub_right Fs
    · exact (A.lowS.symm.sub_left ws).sub_right Bs
  · apply BitVec.eq_of_toNat_eq
    rw [hr, toNat_ofNat_lt (Nat.lt_of_le_of_lt (candidateStatus_le _) (by decide))]
    rfl
  · show Spec.Rsa.bytesAt u.mem ((arg o 0).setWidth 64) (arg o 1).toNat = _
    rw [← hm₂]; exact hout
  · have w1 : Spec.Rsa.wordsAt s₂.mem (addr (arg o 9) candOff) 1 =
        [s₂.mem.readW (addr (arg o 9) candOff + BitVec.ofNat 64 0) 64] := rfl
    rw [show (arg o 9 + BitVec.ofNat 32 candOff).setWidth 64 = addr (arg o 9) candOff from rfl, w1,
      BitVec.add_zero, List.cons.injEq] at hw
    rw [← hm₂]
    refine (halves hw.1 ?_).1.trans ?_
    · split <;> (have := (arg o 6).isLt; omega_arith)
    · unfold candUsed
      rw [rand_length]
      rfl

theorem body_noSp :
    NoSp (Code.seq (.block arguments)
      (.call Spec.Ffdh.sievedParameterCandidateApi.name Impl.Ffdh.X86.Candidate.code) : Prog isa) :=
  NoSp.of_all (by rsa_stack_shape)

/-- Back from the frame. -/
theorem Fr.free {o s : State} {ds : List Nat} {f : Nat → BitVec 32} (h : Fr o ds f s) :
    St o ds f (freed argsBytes s) := by
  refine ⟨h.abi, h.rd, by rw [freed_wr, h.wr]; rfl, h.syms, ?_,
    by rw [freed_gpr _ _ (by decide), h.esi], fun r hr hne => ?_, h.frame, h.words⟩
  · rw [freed_esp, h.esp, BitVec.sub_add_cancel]
  · by_cases hsp : r = .esp
    · subst hsp; rw [freed_esp, h.esp, BitVec.sub_add_cancel]
    · rw [freed_gpr _ _ hsp, h.saved r hr hne hsp]

theorem attempt_ok {p : PPub} {o s : State} {used n : Nat} (h : Live p o used n s) (hu : used < p.randLen) :
    WP isa attempt s fun u => St o liveDs (liveF p (o.gpr .esi) used n) u ∧
      u.gpr .eax = BitVec.ofNat 32 (candidateStatus (candOf o used)) ∧ AttemptOut o used u.mem ∧
      u.mem.readW (addr (arg o 9) candOff) 32 = BitVec.ofNat 32 (candUsed p.bits p.gen p.rand used) := by
  have S := h.st
  obtain ⟨A, rfl⟩ := h.input
  have h1 : 212 ≤ (o.gpr .esp).toNat := A.stackLow
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by rw [S.esp]; unfold argsBytes; omega_arith) body_noSp ?_
  refine WP.seq (WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ?_)
  exact WP.mono (call_ok F hu a) fun u ⟨F', e, out, cu⟩ =>
    ⟨F'.free, by rw [freed_gpr _ _ (by decide)]; exact e, by rw [freed_mem]; exact out, by rw [freed_mem]; exact cu⟩

end VG.Proof.Ffdh.X86.PSearch
