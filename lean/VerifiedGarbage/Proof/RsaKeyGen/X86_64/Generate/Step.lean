module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.KeyRun
import VerifiedGarbage.Proof.RsaKeyGen.InitWords
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-! # After a prime's search

The loop's states: one about to search (`GenIter`, from `Data.lean`), with a
measure that each step that goes on lowers (`genMeasure`), and one that ended
the key search with `final` (`GenDone`). After a search and the count of the
octets it consumed (`Mid`): the frame for the octets consumed so far and the
search's counted candidates left, the search's status and consumption in
registers, and the key's buffer.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

/-- A loop state that ended the key search with `final`: the frame for its
consumption and its state for the next call, its status in the frame, the
key's buffer, and its request in the state. -/
def GenDone (p : GenPublic) (original : State) (final : KeySearchResult) (s : State) : Prop :=
  GenFrame p original final.used final.progress s ∧ word s.mem p.F 80 = BitVec.ofNat 64 final.keyStatus ∧
    Spec.Rsa.bytesAt s.mem p.kp (9 * p.L) = keySearchBytes p.L final ∧
    ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested

/-- What each step that goes on lowers: the octets left of the tape, then the
generations left. -/
def genMeasure (p : GenPublic) (used : Nat) (st : KeyProgress) : Nat := (p.randLen - used) * 2 ^ 64 + st.left

/-- The loop's invariant, at the measure `n`. -/
def GenInv (p : GenPublic) (original : State) (final : KeySearchResult) (n : Nat) (s : State) : Prop :=
  ∃ used st, n = genMeasure p used st ∧ GenIter p original final used st s

/-- What a prime's search leaves: its prime's octets, or zeros. -/
def outBytes (L : Nat) (r : PrimeSearchResult) : List Byte :=
  match r.outcome with
  | .accepted c => Spec.Rsa.i2osp c L
  | _ => List.replicate L 0

/-- The search of the progress' prime from octet `used`. -/
abbrev rOf (p : GenPublic) (original : State) (used : Nat) (st : KeyProgress) : PrimeSearchResult :=
  primeOf p.L p.eB st ((genRand original).drop used)

/-- After a search and the count of the octets it consumed. -/
structure Mid (p : GenPublic) (original : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (u : State) : Prop where
  frame : GenFrame p original (used + (rOf p original used st).used)
    ⟨st.left, st.phase, (rOf p original used st).remaining⟩ u
  final : ∃ tr, final = (tailOf p original used st).consume used tr
  low : Spec.Rsa.bytesAt u.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0
  slot4 : Spec.Rsa.bytesAt u.mem (p.slot 4) p.L =
    (match st.phase with
      | .p => outBytes p.L (rOf p original used st)
      | .q pB => pB)
  slot5 : Spec.Rsa.bytesAt u.mem (p.slot 5) p.L =
    (match st.phase with
      | .p => List.replicate p.L 0
      | .q _ => outBytes p.L (rOf p original used st))
  high : Spec.Rsa.bytesAt u.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0
  req : ∃ requested, word u.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (rOf p original used st).Requests (primeEntropy p.L) requested

/-! ## The key's buffer -/

theorem bytesAt_add (m : Mem) (a : Addr) (x y : Nat) :
    Spec.Rsa.bytesAt m a (x + y) = Spec.Rsa.bytesAt m a x ++ Spec.Rsa.bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

/-- The key's buffer: the low four slots, `p`'s, `q`'s and the high three. -/
theorem key_bytes (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m p.kp (9 * p.L) = Spec.Rsa.bytesAt m p.kp (4 * p.L) ++
      Spec.Rsa.bytesAt m (p.slot 4) p.L ++ Spec.Rsa.bytesAt m (p.slot 5) p.L ++
      Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) := by
  rw [show 9 * p.L = 4 * p.L + p.L + p.L + 3 * p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show 4 * p.L + p.L = 5 * p.L by omega, show 5 * p.L + p.L = 6 * p.L by omega]

/-- The key's buffer, as the key's outputs. -/
theorem key_outs (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m p.kp (9 * p.L) =
      ((keyOutsOf p).map fun o => Spec.Rsa.bytesAt m o.1 o.2).flatten := by
  simp only [keyOutsOf, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show 9 * p.L = 2 * p.L + 2 * p.L + p.L + p.L + p.L + p.L + p.L by omega]
  rw [bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add,
    show 2 * p.L + 2 * p.L = 4 * p.L by omega, show 4 * p.L + p.L = 5 * p.L by omega,
    show 5 * p.L + p.L = 6 * p.L by omega, show 6 * p.L + p.L = 7 * p.L by omega,
    show 7 * p.L + p.L = 8 * p.L by omega]
  simp only [List.append_assoc]

/-! ## After the search -/

section

variable {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}

/-- A region of the key's buffer apart from the search's output is kept
through the search. -/
theorem search_kept (h : GenLive p original used st s) (hm : Frame (searchChanges p st) s.mem t.mem)
    {R : Region} (hR : Region.Sub R (cK p)) (hO : R.Disjoint (rO p st)) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have hf := h.input.cfacts
  have hst := hf.stack
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
  obtain ⟨sK, -, -, -, -⟩ := hst
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  refine hm.bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hO
  · exact hf.kU.sub_left hR
  · exact hf.kS.sub_left hR
  · exact (hf.kT.sub_left hR).sub_right rT_sub
  · exact (sK.sub_left hR).sub_right
      (show Region.Sub (⟨p.sp - BitVec.ofNat 64 552, 392⟩ : Region) (cStack p) from Region.sub_prefix (by decide))

theorem genRand_length (h : GenFrame p original used st s) : (genRand original).length = p.randLen := by
  rw [← h.random]; simp [Spec.Rsa.bytesAt]

theorem rOf_used_le (h : GenFrame p original used st s) : used + (rOf p original used st).used ≤ p.randLen := by
  have h2 : (rOf p original used st).used ≤ p.randLen - used := by
    have := primeSearch_used_le p.L p.eB st.phase.other st.remaining ((genRand original).drop used)
    rw [List.length_drop, genRand_length h] at this
    exact this
  have := h.used_le
  omega

/-- The key's buffer and the state's request through the count of the octets
consumed. -/
theorem head_kept (h : GenFrame p original used st s) {u : State} {v : BitVec 64}
    (hm : u.mem = writeFrame s.mem p.F [(8, v)]) {R : Region} (hR : Region.Sub R (cK p)) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  rw [hm]
  exact bytes_kept (writeFrame_frame _ _ _ fun e he => by
    obtain rfl := List.mem_singleton.mp he; show 8 < 20; decide) (h.frame_key.sub_right hR) hn

theorem slot_disj (hf : CFacts p) {i j a b : Nat} (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L)
    (ha : i * p.L + a ≤ 9 * p.L) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.slot i, a⟩ : Region).Disjoint ⟨p.slot j, b⟩ := kk hf h ha hb

theorem low_disj (hf : CFacts p) {j b : Nat} (h : 4 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
    (⟨p.kp, 4 * p.L⟩ : Region).Disjoint ⟨p.slot j, b⟩ := by
  have := slot_disjoint p.kp (d := 0) (n := 4 * p.L) (e := j * p.L) (k := b)
    (.inl (by have := Nat.mul_le_mul_right p.L h; omega)) (by have := hf.nK; omega) (by have := hf.nK; omega)
  rwa [← kp_zero] at this

end

/-- The status and the count of the octets consumed, after the search. -/
theorem after_head {p : GenPublic} {original s t : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (hi : GenIter p original final used st s) (ha : AfterSearch p original used st s t) :
    WP isa (.block [.mov32 .rax (.reg .rax), .mov .rcx (.mem (field 2)), .mov .rcx (.mem { base := .rcx }),
      .mov .rdx (.mem (field 8)), .alu .add .rdx (.reg .rcx), .store (field 8) .rdx,
      .alu .test .rax (.reg .rax)]) t fun u =>
      eval .e u = some (decide ((rOf p original used st).status = 0)) ∧
        u.gpr .rax = BitVec.ofNat 64 (rOf p original used st).status ∧
        u.gpr .rcx = BitVec.ofNat 64 (rOf p original used st).used ∧ Mid p original final used st u := by
  obtain ⟨hl, hfin⟩ := hi
  have hf := hl.input.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  have hle := rOf_used_le hl.toGenFrame
  refine WP.mono (head_ok ha.frame ha.status ha.usedw) fun u ⟨⟨he, hax, hcx, hm⟩, k⟩ => ⟨he, hax, hcx, ?_⟩
  rw [SearchInit.add_ofNat] at hm
  have hb : ∀ e ∈ [(8, BitVec.ofNat 64 (used + (rOf p original used st).used))], e.1 < 20 := by
    intro e he; obtain rfl := List.mem_singleton.mp he; show 8 < 20; decide
  have hhead : ∀ {R : Region}, Region.Sub R (cK p) → R.len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt t.mem R.base R.len :=
    fun hR hn => head_kept ha.frame hm hR hn
  have hkey := hl.key
  have hph := phaseWord_le st.phase
  -- The key's buffer after the search.
  have hlow : Spec.Rsa.bytesAt t.mem p.kp (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [← hkey.low]
    refine search_kept hl ha.mem (R := ⟨p.kp, 4 * p.L⟩) (Region.sub_prefix (by omega)) ?_ (by
      show 4 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
    unfold rO outOf; split
    · exact low_disj hf (by decide) (by omega)
    · exact low_disj hf (by decide) (by omega)
  have hsplit : Spec.Rsa.bytesAt s.mem (p.slot 5) (4 * p.L) =
      Spec.Rsa.bytesAt s.mem (p.slot 5) p.L ++ Spec.Rsa.bytesAt s.mem (p.slot 6) (3 * p.L) := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega]
  have hhigh5 := hkey.high
  rw [hsplit, show 4 * p.L = p.L + 3 * p.L by omega, ← List.replicate_append_replicate] at hhigh5
  obtain ⟨h5s, h6s⟩ := List.append_inj hhigh5 (by simp [Spec.Rsa.bytesAt]) |>.imp id id
  have hhigh : Spec.Rsa.bytesAt t.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0 := by
    rw [← h6s]
    refine search_kept hl ha.mem (R := ⟨p.slot 6, 3 * p.L⟩) (kSlot_sub (by omega)) ?_ (by
      show 3 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
    unfold rO outOf; split
    · exact slot_disj hf (by omega) (by omega) (by omega)
    · exact slot_disj hf (by omega) (by omega) (by omega)
  have hout := ha.out
  have hs4 : Spec.Rsa.bytesAt t.mem (p.slot 4) p.L =
      (match st.phase with
        | .p => outBytes p.L (rOf p original used st)
        | .q pB => pB) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      have ho : outOf p ⟨left, .p, remaining⟩ = p.slot 4 := rfl
      rw [ho] at hout
      rw [hout]; rfl
    | q pB =>
      rw [← hkey.other pB rfl]
      exact search_kept hl ha.mem (R := ⟨p.slot 4, p.L⟩) (kSlot_sub (by omega))
        (slot_disj hf (by omega) (by omega) (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)
  have hs5 : Spec.Rsa.bytesAt t.mem (p.slot 5) p.L =
      (match st.phase with
        | .p => List.replicate p.L 0
        | .q _ => outBytes p.L (rOf p original used st)) := by
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      rw [← h5s]
      exact search_kept hl ha.mem (R := ⟨p.slot 5, p.L⟩) (kSlot_sub (by omega))
        (slot_disj hf (by omega) (by omega) (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)
    | q pB =>
      have ho : outOf p ⟨left, .q pB, remaining⟩ = p.slot 5 := rfl
      rw [ho] at hout
      rw [hout]; rfl
  obtain ⟨req, hreq, hreqs⟩ := ha.req
  refine ⟨ha.frame.store hle _ hb (by intro e he; obtain rfl := List.mem_singleton.mp he; show 9 ≠ 8; decide) hm k.2.1 k.2.2
      (fun r hr => k.gpr (by revert r; decide)) (by rw [hm]; exact slots_used ha.frame _ [] (by simp) (by simp)),
    hfin, ?_, ?_, ?_, ?_, ⟨req, ?_, hreqs⟩⟩
  · rw [hhead (R := ⟨p.kp, 4 * p.L⟩) (Region.sub_prefix (by omega)) (by show 4 * p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hlow
  · rw [hhead (R := ⟨p.slot 4, p.L⟩) (kSlot_sub (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hs4
  · rw [hhead (R := ⟨p.slot 5, p.L⟩) (kSlot_sub (by omega)) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hs5
  · rw [hhead (R := ⟨p.slot 6, 3 * p.L⟩) (kSlot_sub (by omega)) (by show 3 * p.L ≤ 2 ^ 64; have := hf.nK; omega)]
    exact hhigh
  · rw [hm]
    refine Eq.trans ((writeFrame_frame _ _ _ hb).readW (r := cS p) (a := p.stp + BitVec.ofNat 64 24) (w := 64)
      (Offset.contains_base p.stp (d := 24) (n := 8) (k := 56) (by decide) (by have := hf.nT; omega))
      (fun q hq => ?_) (by decide)) hreq
    obtain rfl := List.mem_singleton.mp hq
    exact ha.frame.state_frame.symm

/-- A frame through a step that changes no memory and keeps the regions and
the callee-saved registers. -/
theorem GenFrame.keep {p : GenPublic} {original s t : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p original used st s) (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (hg : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : GenFrame p original used st t := by
  refine ⟨h.input, h.used_le, hr.trans h.rd, hw.trans h.wr, (hg .rsp (by decide)).trans h.rsp,
    (hg .r12 (by decide)).trans h.r12, fun reg hreg hne hs => (hg reg hreg).trans (h.saved reg hreg hne hs),
    ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.savedR12, h.random, h.headers, h.state]

theorem Mid.keep {p : GenPublic} {original u v : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (h : Mid p original final used st u) (hm : v.mem = u.mem) (hr : v.rd = u.rd)
    (hw : v.wr = u.wr) (hg : ∀ r ∈ calleeSaved, v.gpr r = u.gpr r) : Mid p original final used st v := by
  refine ⟨h.frame.keep hm hr hw hg, h.final, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [hm]
  exacts [h.low, h.slot4, h.slot5, h.high, h.req]

end VG.Proof.RsaKeyGen.X86_64.Generate
