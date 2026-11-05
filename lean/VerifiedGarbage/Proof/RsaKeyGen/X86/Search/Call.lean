module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CallPre
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CallPre
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.CallWith

-- separate module: the search's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # The candidate's call (i686)

`vg_rsa_keygen_candidate`, called in its frame of arguments for the rest of
the tape, returns the status of the candidate there, writes its output and
the octets it consumed (to `used`), and changes memory only at those, the
working space and the stack the search uses (`candidateRun_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Impl.RsaKeyGen.X86.Search
open VG.Spec.RsaKeyGen (candidateOp candidateStatus)

/-- What the candidate leaves: its status, its output and the octets it
consumed. -/
def CandPost (p : SearchPublic) (pB rand : List Byte) (used : Nat) (t : State) : Prop :=
  (t.gpr .eax).toNat = candidateStatus (candidateOp p.len p.eB pB (rand.drop used)) ∧
    Spec.Rsa.bytesAt t.mem (p.op.setWidth 64) p.len =
      (match candidateOp p.len p.eB pB (rand.drop used) with
        | some (.prime c, _) => Spec.Rsa.i2osp c p.len
        | _ => List.replicate p.len 0) ∧
    Spec.Rsa.wordsAt t.mem (p.up.setWidth 64) 1 =
      [BitVec.ofNat 64 (match candidateOp p.len p.eB pB (rand.drop used) with
        | some (_, rest) => (p.randLen - used) - rest.length
        | none => 0)]

theorem bytesAt_drop (m : Mem) (P : Addr) (k n : Nat) :
    Spec.Rsa.bytesAt m (P + BitVec.ofNat 64 k) (n - k) = (Spec.Rsa.bytesAt m P n).drop k := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_drop,
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rd_eq {o : State} (A : SearchABI o) : o.rd = [eR o, pR o, rR o, tR o] := by
  have hp := A.rdPrefix
  have hd := A.rdTable
  rw [← List.take_append_drop (o.rd.length - 1) o.rd, hp, hd]
  simp only [tableRegions, Abi.constRegions_cons, Abi.constRegions_nil,
    VG.Proof.RsaKeyGen.X86.Candidate.packed_length]
  rfl

/-- The regions of the call, among those of a state in the frame. -/
theorem call_covers {p : SearchPublic} {o s₀ u : State} {used : Nat} (h : Fr p o s₀ u)
    (hu : used < (arg o 8).toNat) :
    Covers (callRd o used ++ callWr o) (u.rd ++ u.wr) ∧ Covers (callWr o) u.wr := by
  have A := h.input.abi
  have hw : ∀ r ∈ callWr o, ∃ r' ∈ u.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := by
    intro r hr
    rw [h.wr, A.wr]
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨oR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨uR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨bR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨frR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub hw⟩
  rcases List.mem_append.mp hr with hr | hr
  · rw [h.rd, rd_eq A]
    rw [callRd, tableRs_eq] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨eR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨pR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨rR o, by simp, used, win_base A hu, show used + ((arg o 8).toNat - used) ≤ (arg o 8).toNat by omega⟩
    · exact ⟨tR o, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
  · obtain ⟨r', hr', off, hb⟩ := hw r hr
    exact ⟨r', List.mem_append_right _ hr', off, hb⟩

theorem body_noSp (c : Cand) : NoSp (.seq (.block arguments) c.call) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · have h : (Code.block arguments : Prog isa).allInstrs (fun i => !Taint.clobbers i .esp) = true := by decide
    rw [Code.allInstrs_eq] at h
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi
  · exact c.noSp i hi

/-- The saved registers, through writes apart from the push's frame. -/
theorem saved_frame {p : SearchPublic} {o : State} (h : SearchInput p o) {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨low o + BitVec.ofNat 64 200, 16⟩ r) {m m' : Mem} (hf : Frame rs m m')
    (hs : Saved m p.S1 o) : Saved m' p.S1 o := by
  have A := h.abi
  have hl := low_toNat A
  have h1 := A.stackLow
  have hb := A.stackBound
  have keep (k : Nat) (hk : k < 4) : m'.readW ((p.S1 + BitVec.ofNat 32 (4 * k)).setWidth 64) 32 =
      m.readW ((p.S1 + BitVec.ofNat 32 (4 * k)).setWidth 64) 32 := by
    rw [saved_addr h hk]
    exact hf.readW (Offset.contains _ (by omega) (by omega) (by omega)) hd (by decide)
  obtain ⟨h0, h1, h2, h3⟩ := hs
  exact ⟨(keep 0 (by decide)).trans h0, (keep 1 (by decide)).trans h1, (keep 2 (by decide)).trans h2,
    (keep 3 (by decide)).trans h3⟩

/-- The `n ≤ 156` bytes below the call's stack pointer. -/
theorem below_call {p : SearchPublic} {o u : State} (h : SearchInput p o) (he : u.gpr .esp = p.S2) {n : Nat}
    (hn : n ≤ 156) : below (u.gpr .esp) n = ⟨low o + BitVec.ofNat 64 (156 - n), n⟩ := by
  have A := h.abi
  rw [he, SearchPublic.S2, h.sp_eq]
  change (⟨(o.gpr .esp - BitVec.ofNat 32 60 - BitVec.ofNat 32 n).setWidth 64, n⟩ : Region) = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]
  have e := addr_sub A (k := 60 + n) (d := 0) (by omega) (by omega)
  simp only [addr, BitVec.add_zero] at e
  rw [e, show 216 - (60 + n) + 0 = 156 - n by omega]

/-- What the candidate reads, on its entry, with its return address
written: the search's. -/
theorem entry_read {p : SearchPublic} {o s₀ u : State} (F : Fr p o s₀ u) (v : BitVec 32) {r : Region}
    (hr : r = eR o ∨ r = pR o ∨ r = rR o) (hlr : (lowR o).Disjoint r) (hn : r.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (u.mem.writeW (low o + 152#64) v) r.base r.len = Spec.Rsa.bytesAt o.mem r.base r.len := by
  have Rs : Region.Sub ⟨low o + BitVec.ofNat 64 152, 4⟩ (lowR o) := low_sub (by decide)
  have fe : Frame [⟨low o + BitVec.ofNat 64 152, 4⟩] u.mem (u.mem.writeW (low o + 152#64) v) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have e1 : Spec.Rsa.bytesAt (u.mem.writeW (low o + 152#64) v) r.base r.len =
      Spec.Rsa.bytesAt u.mem r.base r.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact fe.bytes (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact (hlr.sub_left Rs).symm) hn
      (List.mem_range.mp hi)
  rw [e1, F.input.bytes_frame hr hn F.frame]

/-- `e`, `p` and the rest of the tape, as the candidate reads them. -/
theorem entry_bytes {p : SearchPublic} {o s₀ u : State} {used : Nat} (F : Fr p o s₀ u)
    (hu : used < (arg o 8).toNat) (v : BitVec 32) :
    Spec.Rsa.bytesAt (u.mem.writeW (low o + 152#64) v) ((arg o 3).setWidth 64) (arg o 4).toNat = searchE o ∧
    Spec.Rsa.bytesAt (u.mem.writeW (low o + 152#64) v) ((arg o 5).setWidth 64) (arg o 6).toNat = searchP o ∧
    Spec.Rsa.bytesAt (u.mem.writeW (low o + 152#64) v)
      ((arg o 7 + BitVec.ofNat 32 used).setWidth 64) (arg o 8 - BitVec.ofNat 32 used).toNat =
        (searchRand o).drop used := by
  have A := F.input.abi
  have rB := A.rBound
  have hlen : (arg o 8 - BitVec.ofNat 32 used).toNat = (arg o 8).toNat - used := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by have := (arg o 8).isLt; omega)]
    have := (arg o 8).isLt; omega
  have eRand := entry_read F v (r := rR o) (.inr (.inr rfl)) A.lowRand (by change (arg o 8).toNat ≤ _; omega)
  refine ⟨entry_read F v (r := eR o) (.inl rfl) A.lowE (by have := A.eBound; change (arg o 4).toNat ≤ _; omega),
    entry_read F v (r := pR o) (.inr (.inl rfl)) A.lowP (by have := A.pBound; change (arg o 6).toNat ≤ _; omega), ?_⟩
  rw [hlen, win_base A hu, bytesAt_drop]
  exact congrArg (List.drop used) eRand

theorem candidateRun_ok (c : Cand) {p : SearchPublic} {o s : State} {used remaining : Nat}
    (h : SearchLive p o used remaining s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (candidateRun c.call) s fun t =>
      SearchLive p o used remaining t ∧ CandPost p (searchP o) (searchRand o) used t := by
  have hb := h.toSearchBase
  have hi := hb.input
  have A := hi.abi
  have hv := hi.len_valid
  have h1 : 216 ≤ (o.gpr .esp).toNat := A.stackLow
  have hpr : p.randLen = (arg o 8).toNat := by rw [← hi.2]; rfl
  have hsn : (s.gpr .esp).toNat = (o.gpr .esp).toNat - 16 := by
    rw [hb.sp, SearchPublic.S1, hi.sp_eq]; exact VG.X86.sub_toNat (by omega)
  unfold candidateRun
  rw [show 4 * callWords = 44 from rfl]
  refine WP.frameAlloc (by decide) (by decide) (by decide) (by omega) (body_noSp c) ?_
  refine WP.seq (WP.mono (arguments_ok hb.alloc h.esi) fun u ⟨F, a⟩ => ?_)
  obtain ⟨cov, covW⟩ := call_covers F (used := used) (by omega)
  have hun : (u.gpr .esp).toNat = (o.gpr .esp).toNat - 60 := by
    rw [F.esp, SearchPublic.S2, hi.sp_eq]; exact VG.X86.sub_toNat (by omega)
  refine WP.of_syms (WP.call c.verified.1 c.noSp (by have := c.stack; omega)
    (call_pre hi hroom F.esp a F.syms F.frame) cov covW fun u' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ sy => ?_)
  have hp := hpost
  sig_post [VG.Proof.RsaKeyGen.X86.Candidate.contract, Spec.RsaKeyGen.candidateContract,
    Spec.RsaKeyGen.candidateSig, abi, argSlots, argVal, argBytes, Abi.withConsts,
    VG.Impl.RsaKeyGen.TrialTable32.consts] at hp
  simp only [ce_arg hi F.esp a _ _ (show 0 < 11 by decide), ce_arg hi F.esp a _ _ (show 1 < 11 by decide),
    ce_arg hi F.esp a _ _ (show 2 < 11 by decide), ce_arg hi F.esp a _ _ (show 3 < 11 by decide),
    ce_arg hi F.esp a _ _ (show 4 < 11 by decide), ce_arg hi F.esp a _ _ (show 5 < 11 by decide),
    ce_arg hi F.esp a _ _ (show 6 < 11 by decide), ce_arg hi F.esp a _ _ (show 7 < 11 by decide),
    ce_arg hi F.esp a _ _ (show 8 < 11 by decide), callArg, Nat.reduceEqDiff, ↓reduceIte,
    ret_addr hi F.esp] at hp
  -- what the callee read
  have hl := low_toNat A
  have hsl := c.stack
  have rB := A.rBound
  have hlen : (arg o 8 - BitVec.ofNat 32 used).toNat = (arg o 8).toNat - used := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := used) (by have := (arg o 8).isLt; omega)]
    have := (arg o 8).isLt; omega
  obtain ⟨eE, eP, eW⟩ := entry_bytes F (used := used) (by omega) (u.unknowns 0)
  simp only [eE, eP, eW] at hp
  have hpl : p.len = (arg o 1).toNat := by rw [← hi.2]; rfl
  have heB : p.eB = searchE o := by rw [← hi.2]; rfl
  have hop : p.op = arg o 0 := by rw [← hi.2]; rfl
  have hup : p.up = arg o 2 := by rw [← hi.2]; rfl
  rw [← hpl, ← heB, hlen, ← hpr] at hp
  obtain ⟨hr, hout, hw⟩ := hp
  rw [BitVec.setWidth_append_eq_right, hg₂ .eax (by decide)] at hr
  have keep (r : Reg) (hr : r ∈ calleeSaved) (hne : r ≠ .esp) : (freed 44 u').gpr r = s.gpr r := by
    rw [freed_gpr _ _ hne, hcs r hr, F.keep r (by revert hr; revert hne; cases r <;> decide) hne]
  have bc := below_call hi F.esp (n := stackUse c.code + 4) (by omega)
  have Fs : Region.Sub (frR o) (lowR o) := low_sub (by decide)
  have Bs : Region.Sub (below (u.gpr .esp) (stackUse c.code + 4)) (lowR o) := by
    rw [bc]; exact low_sub (by omega)
  have Ps : Region.Sub ⟨low o + BitVec.ofNat 64 200, 16⟩ (lowR o) := low_sub (by decide)
  have fr : Frame (changes o) u.mem u'.mem := hf.sub fun r hr => by
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨oR o, by simp [changes], fun _ h => h⟩
    · exact ⟨uR o, by simp [changes], fun _ h => h⟩
    · exact ⟨bR o, by simp [changes], fun _ h => h⟩
    · exact ⟨below (o.gpr .esp) 216, by simp [changes], by rw [← hi.low_eq]; exact Fs⟩
    · exact ⟨below (o.gpr .esp) 216, by simp [changes], by rw [← hi.low_eq]; exact Bs⟩
  have sv : Saved u'.mem p.S1 o := saved_frame hi (fun r hr => by
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact A.lowO.sub_left Ps
    · exact A.lowU.sub_left Ps
    · exact A.lowB.sub_left Ps
    · exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · rw [bc]; exact Offset.disjoint _ (by omega) (by omega) (by omega)) hf F.saved
  refine ⟨⟨⟨hi, hrd.trans F.rd, ?_, sy.trans F.syms, ?_, sv, F.frame.trans fr⟩, h.used_le, h.remaining_le,
    (keep .esi (by decide) (by decide)).trans h.esi, (keep .edi (by decide) (by decide)).trans h.edi,
    (keep .ebx (by decide) (by decide)).trans h.ebx⟩, ?_, ?_, ?_⟩
  · change u'.wr.tail = _
    rw [hwr, F.wr]; rfl
  · rw [freed_esp, hcs .esp (by decide), F.esp, S2_eq p, BitVec.sub_add_cancel]
  · rw [freed_gpr _ _ (by decide)]; exact hr
  · change Spec.Rsa.bytesAt u'.mem _ _ = _
    rw [hop, ← hm₂]; exact hout
  · change Spec.Rsa.wordsAt u'.mem _ _ = _
    rw [hup, ← hm₂]; exact hw

end VG.Proof.RsaKeyGen.X86.Search
