module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.KeyRun
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.KeyRun
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Spec.RsaKeyGen.GenerationAgrees

/-! # The controller's steps and loop (i686)

What follows each prime's search and the key, the stores to the state, and
the loop.
-/

@[expose] public section

/-! ## After a prime's search (i686)

The octets the search consumed added to `esi`, its status against 0 (`head`),
and the state that leaves (`Mid`): the frame for the octets consumed so far
and the search's counted candidates left, its status and consumption in
registers, and the key's buffer.
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

/-- What a prime's search leaves: its prime's octets, or zeros. -/
def outBytes (L : Nat) (r : PrimeSearchResult) : List Byte :=
  match r.outcome with
  | .accepted c => Spec.Rsa.i2osp c L
  | _ => List.replicate L 0

/-- After a search and the count of the octets it consumed. -/
structure Mid (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (u : State) : Prop where
  frame : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ u
  ebx : u.gpr .ebx = 4
  status : (u.gpr .eax).toNat = (rOf p o used st).status
  ecx : u.gpr .ecx = BitVec.ofNat 32 (rOf p o used st).used
  final : ∃ tr, final = (tailOf p o used st).consume used tr
  low : Spec.Rsa.bytesAt u.mem (p.kp.setWidth 64) (4 * p.L) = List.replicate (4 * p.L) 0
  slot4 : Spec.Rsa.bytesAt u.mem (p.slot 4) p.L =
    (match st.phase with
      | .p => outBytes p.L (rOf p o used st)
      | .q pB => pB)
  slot5 : Spec.Rsa.bytesAt u.mem (p.slot 5) p.L =
    (match st.phase with
      | .p => List.replicate p.L 0
      | .q _ => outBytes p.L (rOf p o used st))
  high : Spec.Rsa.bytesAt u.mem (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0
  req : ∃ requested, word u.mem p.stp 24 = BitVec.ofNat 64 requested ∧
    (rOf p o used st).Requests (primeEntropy p.L) requested

theorem bytesAt_add (m : Mem) (a : Addr) (x y : Nat) :
    Spec.Rsa.bytesAt m a (x + y) = Spec.Rsa.bytesAt m a x ++ Spec.Rsa.bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, Offset.add_add]

theorem slot_add (p : GenPublic) (j n : Nat) : p.slot j + BitVec.ofNat 64 (n * p.L) = p.slot (j + n) := by
  rw [GenPublic.slot, GenPublic.slot, Offset.add_add, Nat.add_mul]

theorem outOf_zero (p : GenPublic) : outOf p 0 = p.slot 4 := by
  simp only [outOf, pLenOf, ↓reduceIte, Nat.add_zero]

theorem outOf_one (p : GenPublic) : outOf p 1 = p.slot 5 := by
  simp only [outOf, pLenOf, Nat.one_ne_zero, ↓reduceIte]
  congr 2; omega

/-- A part of the key's buffer apart from the search's output is kept
through the search. -/
theorem search_kept {p : GenPublic} {o s t : State} {ph : Nat} (hi : GenInput p o)
    (hm : Frame (searchChanges p o ph) s.mem t.mem) {R : Region} (hR : Region.Sub R (kR o))
    (hO : R.Disjoint ⟨outOf p ph, p.L⟩) (hn : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  have A := hi.abi
  refine bytes_keep hm (fun q hq => ?_) hn
  simp only [searchChanges, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact hO
  · exact A.ku.sub_left hR
  · exact A.kb.sub_left hR
  · exact (A.ks.sub_left hR).sub_right (by rw [hi.sR_eq]; exact Region.sub_prefix (by decide))
  · rw [← hi.low_eq]; exact A.lowK.symm.sub_left hR

theorem genRand_length {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s) :
    (genRand o).length = p.randLen := by
  rw [← h.random]; simp [Spec.Rsa.bytesAt]

theorem rOf_used_le {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s) :
    used + (rOf p o used st).used ≤ p.randLen := by
  have h2 : (rOf p o used st).used ≤ p.randLen - used := by
    have := Spec.RsaKeyGen.primeSearch_used_le p.L p.eB st.phase.other st.remaining ((genRand o).drop used)
    rw [List.length_drop, genRand_length h] at this
    exact this
  have := h.used_le
  omega

/-- The search's consumption added to `esi`, and its status against 0. -/
theorem head_ok {p : GenPublic} {o s t : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}
    (hi : GenIter p o final used st s) (ha : AfterSearch p o used st s t) :
    WP isa (.block [.mov .edx (.mem (param 0 2)), .mov .ecx (.mem (at_ .edx 0)), .alu .add .esi (.reg .ecx),
        .alu .cmp .eax (.imm 0)]) t
      fun u => Mid p o final used st u ∧ u.zf = some (decide ((rOf p o used st).status = 0)) := by
  obtain ⟨hl, hfin⟩ := hi
  have hf := ha.frame
  have hb := hf.toGenBase
  have hin := hb.input
  have A := hin.abi
  have hle := rOf_used_le hl.toGenFrame
  have hlt := hin.randLen_lt
  have hU : InRegions (t.rd ++ t.wr) ((arg o 2).setWidth 64) 4 :=
    ⟨uR o, by rw [hb.rd, hb.wr, A.wr]; simp, by simp [Region.Contains]⟩
  have hu0 : t.mem.readW ((arg o 2).setWidth 64) 32 = BitVec.ofNat 32 (rOf p o used st).used := by
    have h0 := ha.usedw
    simp only [word, BitVec.add_zero] at h0
    rw [hin.up_eq] at h0
    exact low_half h0
  refine WP.mono (WP.blockKeep [.eax, .edx, .ecx, .esi] (Q := fun u =>
      u.gpr .esi = BitVec.ofNat 32 used + BitVec.ofNat 32 (rOf p o used st).used ∧
      u.gpr .ecx = BitVec.ofNat 32 (rOf p o used st).used ∧ u.gpr .eax = t.gpr .eax ∧
      u.zf = some (t.gpr .eax - 0 == 0) ∧ u.mem = t.mem) ?_ (by rfl)) fun u ⟨⟨hsi, hcx, hax, hzf, hm⟩, k, sy⟩ => ?_
  · simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 2) (d := 28) rfl, hb.arg_in (i := 2) (by decide),
      hb.arg_val (i := 2) (by decide), BitVec.add_zero, hU, hu0, hf.esi]
  · have hv := hin.len_valid
    have hK := hl.key
    have hu' : u.mem = t.mem := hm
    have zeros_split {m : Mem} {a : Addr} {x y : Nat} (h : Spec.Rsa.bytesAt m a (x + y) = List.replicate (x + y) 0) :
        Spec.Rsa.bytesAt m a x = List.replicate x 0 ∧
          Spec.Rsa.bytesAt m (a + BitVec.ofNat 64 x) y = List.replicate y 0 := by
      rw [bytesAt_add, ← List.replicate_append_replicate] at h
      exact List.append_inj h (by simp [Spec.Rsa.bytesAt])
    have hi5 := zeros_split (x := p.L) (y := 3 * p.L) (by rw [show p.L + 3 * p.L = 4 * p.L by omega]; exact hK.high)
    rw [show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega] at hi5
    have sk (j n : Nat) (hj : j * p.L + n ≤ 9 * p.L) : Region.Sub ⟨p.slot j, n⟩ (kR o) := by
      rw [hin.kR_eq]; exact Offset.sub_base _ hj
    have dj (i j a b : Nat) (h : i * p.L + a ≤ j * p.L ∨ j * p.L + b ≤ i * p.L) (ha : i * p.L + a ≤ 9 * p.L)
        (hb : j * p.L + b ≤ 9 * p.L) : (⟨p.slot i, a⟩ : Region).Disjoint ⟨p.slot j, b⟩ := by
      have := hin.kBound'
      exact Offset.disjoint _ h (by omega) (by omega)
    have dlow (j b : Nat) (h : 4 ≤ j) (hb : j * p.L + b ≤ 9 * p.L) :
        (⟨p.kp.setWidth 64, 4 * p.L⟩ : Region).Disjoint ⟨p.slot j, b⟩ := by
      have := hin.kBound'
      have := Nat.mul_le_mul_right p.L h
      exact Offset.base_disjoint _ (by omega) (by omega)
    have hout := ha.out
    rw [← hu'] at hout
    have hfin' := hfin
    have hreq := ha.req
    rw [← hu'] at hreq
    have F' : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ u :=
      ⟨hb.step k (by decide) sy hm, hle, (k.gpr (by decide)).trans hf.ebp,
        by rw [hsi, ← BitVec.ofNat_add], (k.gpr (by decide)).trans hf.edi, by rw [hu']; exact hf.random,
        by rw [hu']; exact hf.state⟩
    have hbx : u.gpr .ebx = 4 := (k.gpr (by decide)).trans ha.ebx
    have hst : (u.gpr .eax).toNat = (rOf p o used st).status := by rw [hax]; exact ha.status
    have hmem := ha.mem
    refine ⟨?_, ?_⟩
    swap
    · rw [hzf]
      congr 1
      rw [← ha.status]
      by_cases h0 : t.gpr .eax = 0#32
      · simp [h0]
      · have : (t.gpr .eax).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
        simp only [this, decide_false]
        simpa using h0
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      simp only [phaseWord] at hout hmem
      rw [outOf_zero] at hout
      have kept (R : Region) (hR : Region.Sub R (kR o)) (hO : R.Disjoint ⟨p.slot 4, p.L⟩)
          (hn : R.len ≤ 2 ^ 64) : Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
        rw [hu']; exact search_kept hin hmem hR (by rw [outOf_zero]; exact hO) hn
      have e0 := kept ⟨p.kp.setWidth 64, 4 * p.L⟩ (by rw [hin.kR_eq]; exact Region.sub_prefix (by omega))
        (dlow 4 p.L (by decide) (by omega)) (show 4 * p.L ≤ 2 ^ 64 by omega)
      have e5 := kept ⟨p.slot 5, p.L⟩ (sk 5 p.L (by omega)) (dj 5 4 p.L p.L (.inr (by omega)) (by omega) (by omega))
        (show p.L ≤ 2 ^ 64 by omega)
      have e6 := kept ⟨p.slot 6, 3 * p.L⟩ (sk 6 (3 * p.L) (by omega))
        (dj 6 4 (3 * p.L) p.L (.inr (by omega)) (by omega) (by omega)) (show 3 * p.L ≤ 2 ^ 64 by omega)
      exact ⟨F', hbx, hst, hcx, hfin', e0.trans hK.low, hout, e5.trans hi5.1, e6.trans hi5.2, hreq⟩
    | q pB =>
      simp only [phaseWord] at hout hmem
      rw [outOf_one] at hout
      have kept (R : Region) (hR : Region.Sub R (kR o)) (hO : R.Disjoint ⟨p.slot 5, p.L⟩)
          (hn : R.len ≤ 2 ^ 64) : Spec.Rsa.bytesAt u.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
        rw [hu']; exact search_kept hin hmem hR (by rw [outOf_one]; exact hO) hn
      have e0 := kept ⟨p.kp.setWidth 64, 4 * p.L⟩ (by rw [hin.kR_eq]; exact Region.sub_prefix (by omega))
        (dlow 5 p.L (by decide) (by omega)) (show 4 * p.L ≤ 2 ^ 64 by omega)
      have e4 := kept ⟨p.slot 4, p.L⟩ (sk 4 p.L (by omega)) (dj 4 5 p.L p.L (.inl (by omega)) (by omega) (by omega))
        (show p.L ≤ 2 ^ 64 by omega)
      have e6 := kept ⟨p.slot 6, 3 * p.L⟩ (sk 6 (3 * p.L) (by omega))
        (dj 6 5 (3 * p.L) p.L (.inr (by omega)) (by omega) (by omega)) (show 3 * p.L ≤ 2 ^ 64 by omega)
      exact ⟨F', hbx, hst, hcx, hfin', e0.trans hK.low, e4.trans (hK.other pB rfl), hout, e6.trans hi5.2, hreq⟩

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The controller's stores to its state (i686)

Zeros at the key's buffer (`clearAll_ok`); the end of the key search, with a
status (`finish_ok`, `fail_ok`); the next prime's search (`nextPrime_ok`);
and one generation fewer (`dec_ok`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

/-- The whole key's buffer cleared. -/
theorem clearAll_ok {p : GenPublic} {o t : State} {used : Nat} {st : KeyProgress} (hf : GenFrame p o used st t) :
    WP isa clearAll t fun u =>
      GenFrame p o used st u ∧ Frame [kR o] t.mem u.mem ∧
        Spec.Rsa.bytesAt u.mem (p.kp.setWidth 64) (9 * p.L) = List.replicate (9 * p.L) 0 ∧
        Keep [.eax, .ecx, .edx] t u := by
  have hi := hf.input
  have A := hi.abi
  have hv := hi.len_valid
  have hkl : (arg o 1).toNat = 9 * p.L := by rw [A.keyLen, ← hi.L_eq]
  unfold clearAll
  refine WP.seq (WP.mono (WP.blockKeep [.eax, .ecx, .edx] (Q := fun v =>
      v.gpr .edx = arg o 0 ∧ v.gpr .ecx = BitVec.ofNat 32 (9 * p.L) ∧ v.gpr .eax = 0 ∧ v.mem = t.mem) ?_ (by rfl))
    fun v ⟨⟨hd, hc, ha, hm⟩, k, sy⟩ => ?_)
  · simp only [four, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd, List.cons_append, List.nil_append]
    xrun [State.ea, at_, hf.arg_ea (i := 0) (d := 20) rfl, hf.arg_in (i := 0) (by decide),
      hf.arg_val (i := 0) (by decide), hf.ebp, four_val]
    simp only [← BitVec.ofNat_add]; congr 1; omega
  have hfv : GenFrame p o used st v := hf.keyWrite (k.mono (by simp)) sy (R := kR o)
    (fun x hx => hx) (by rw [hm]; exact Frame.refl _ _)
  refine WP.mono_syms (zeroLoop_ok (P := arg o 0) (n := 9 * p.L) (by omega)
    (fun i hi' => (hfv.key_in (by omega))) (by have := A.kBound; omega) (by omega) hd hc ha)
    fun u ⟨fr, hz, ku⟩ sy' => ?_
  have ku' : Keep [.eax, .ecx, .edx] v u := Keep.ofKeeps ku
  have sub : Region.Sub ⟨(arg o 0).setWidth 64, 9 * p.L⟩ (kR o) := fun x hx => by
    simp only [Region.Contains] at hx ⊢; omega
  have fr' : Frame [kR o] v.mem u.mem := fr.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact ⟨kR o, List.mem_singleton_self _, sub⟩
  refine ⟨hfv.keyWrite ku' sy' (fun x hx => hx) fr', by rw [← hm]; exact fr', by rw [hi.kp_eq]; exact hz,
    (k.trans ku').mono (by simp)⟩

/-- A state in the frame, through stores to the state's words from `d`. -/
theorem GenFrame.stateWrite {p : GenPublic} {o t u : State} {used : Nat} {st st' : KeyProgress}
    (hf : GenFrame p o used st t) {rs : List Reg} (k : Keep rs t u) (hrs : ∀ r ∈ rs, r ≠ .esp ∧ r ≠ .ebp ∧
      r ≠ .esi ∧ r ≠ .edi) (sy : u.syms = t.syms) {d n : Nat} (hd : d + n ≤ 56)
    (fr : Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, n⟩] t.mem u.mem) (hst : StateOk p st' u.mem) :
    GenFrame p o used st' u := by
  have hi := hf.input
  have A := hi.abi
  have hS : Region.Sub ⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, n⟩ (sR o) := by
    rw [hi.sR_eq]; exact Offset.sub_base _ hd
  have sv : Saved u.mem p.S1 o := saved_frame hi (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact (A.lowS.sub_left (low_sub (by decide))).sub_right hS) fr hf.saved
  have fc : Frame (changes o) t.mem u.mem := fr.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact ⟨sR o, by simp [changes], hS⟩
  refine ⟨hf.toGenBase.keep k (fun h => (hrs _ h).1 rfl) sy sv fc, hf.used_le,
    (k.gpr fun h => (hrs _ h).2.1 rfl).trans hf.ebp, (k.gpr fun h => (hrs _ h).2.2.1 rfl).trans hf.esi,
    (k.gpr fun h => (hrs _ h).2.2.2 rfl).trans hf.edi, ?_, hst⟩
  rw [← hf.random]
  refine bytes_keep (R := ⟨p.rp.setWidth 64, p.randLen⟩) fr (fun q hq => ?_) (by have := hi.rBound'; simp; omega)
  obtain rfl := List.mem_singleton.mp hq
  rw [← hi.rR_eq]; exact A.rs.sub_right hS

theorem st_slot {B : Addr} {m m' : Mem} {e n d : Nat} (h : Frame [⟨B + BitVec.ofNat 64 e, n⟩] m m')
    (hd : e ≤ d ∧ d + 4 ≤ e + n ∧ e + n < 2 ^ 64) (v : BitVec 32) :
    Frame [⟨B + BitVec.ofNat 64 e, n⟩] m (m'.writeW (B + BitVec.ofNat 64 d) v) :=
  Frame.writeW h (List.mem_singleton_self _) _ (Offset.contains _ hd.1 hd.2.1 hd.2.2)

/-- A 64-bit word of two 32-bit halves. -/
theorem word_halves {m : Mem} {B : Addr} {d : Nat} {lo hi : BitVec 32} (hl : m.readW (B + BitVec.ofNat 64 d) 32 = lo)
    (hh : m.readW (B + BitVec.ofNat 64 (d + 4)) 32 = hi) : m.readW (B + BitVec.ofNat 64 d) 64 = hi ++ lo := by
  rw [Proof.Ffdh.X86.KeyInit.readW64_split, Offset.add_add, hl, hh]

/-- A state word apart from the stores to `[d, d + n)`. -/
theorem word_apart {p : GenPublic} {m m' : Mem} {d n e : Nat}
    (fr : Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, n⟩] m m')
    (he : e + 8 ≤ d ∨ d + n ≤ e) (hn : d + n ≤ 56 ∧ e + 8 ≤ 56) : word m' p.stp e = word m p.stp e :=
  word_keep fr fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    have := p.stp.isLt
    exact Offset.disjoint _ he (by omega) (by omega)

theorem e_apart {p : GenPublic} {m m' : Mem} {d n : Nat}
    (fr : Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, n⟩] m m') (hn : d + n ≤ 48) :
    Spec.Rsa.bytesAt m' (p.stp.setWidth 64 + 48) 8 = Spec.Rsa.bytesAt m (p.stp.setWidth 64 + 48) 8 :=
  bytes_keep (R := ⟨p.stp.setWidth 64 + BitVec.ofNat 64 48, 8⟩) fr (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (show 8 ≤ 2 ^ 64 by decide)

/-- The key search ends with `status`: no phase or generations left. -/
theorem finish_ok {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (hf : GenFrame p o used st s)
    (hr0 : st.remaining = 0) (status : Nat) :
    WP isa (.block (finishWith status)) s fun t =>
      GenFrame p o used ⟨0, .p, 0⟩ t ∧ t.gpr .ebx = BitVec.ofNat 32 status ∧
        Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 32, 16⟩] s.mem t.mem ∧ Keep [.eax, .ecx, .ebx] s t := by
  have hb := hf.toGenBase
  have hi := hb.input
  have hs := hi.sBound'
  refine WP.mono (WP.blockKeep [.eax, .ecx, .ebx] (Q := fun t =>
      t.gpr .ebx = BitVec.ofNat 32 status ∧
      (t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 32 = 0 ∧
        t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 36) 32 = 0 ∧
        t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 40) 32 = 0 ∧
        t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 44) 32 = 0) ∧
      Frame [⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 32, 16⟩] s.mem t.mem) ?_ (by rfl))
    fun t ⟨⟨hbx, ⟨h32, h36, h40, h44⟩, fr⟩, k, sy⟩ => ?_
  · simp only [finishWith, VG.Impl.RsaKeyGen.X86.Generate.st, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 7) (d := 48) rfl, hb.arg_in (i := 7) (by decide),
      hb.arg_val (i := 7) (by decide), st_ea hi (d := 32) (by decide), st_ea hi (d := 36) (by decide),
      st_ea hi (d := 40) (by decide), st_ea hi (d := 44) (by decide), hb.st_inW (d := 32) (n := 4) (by decide),
      hb.st_inW (d := 36) (n := 4) (by decide), hb.st_inW (d := 40) (n := 4) (by decide),
      hb.st_inW (d := 44) (n := 4) (by decide)]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp (disch := decide) only [rdS, rdN]
    · simp (disch := decide) only [rdS, rdN]
    · simp (disch := decide) only [rdS, rdN]
    · simp only [rdS]
    · iterate 4 (refine st_slot ?_ ?hd _; case hd => exact ⟨by decide, by decide, by decide⟩)
      exact Frame.refl _ _
  have hst := hf.state
  rw [← hi.stp_eq] at fr h32 h36 h40 h44
  have z64 : (0 : BitVec 32) ++ (0 : BitVec 32) = BitVec.ofNat 64 0 := by decide
  have hst' : StateOk p ⟨0, .p, 0⟩ t.mem := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _, by decide⟩
    · rw [word_apart fr (.inl (by decide)) (by decide), hst.remaining, hr0]
    · rw [word_apart fr (.inl (by decide)) (by decide)]; exact hst.len
    · rw [word_apart fr (.inl (by decide)) (by decide)]; exact hst.cap
    · exact (word_halves h32 h36).trans z64
    · exact (word_halves h40 h44).trans z64
    · rw [e_apart fr (by decide)]; exact hst.e
  exact ⟨hf.stateWrite k (by decide) sy (by decide) fr hst', hbx, fr, k⟩

theorem pair32 (h l : BitVec 32) : (h ++ l).toNat = h.toNat * 2 ^ 32 + l.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt l.isLt, Nat.shiftLeft_eq]

theorem zero_app {n : Nat} (h : n < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 n = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [pair32, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega),
    show (0 : BitVec 32).toNat = 0 from rfl]
  omega

/-- The high half of a word below `2 ^ 32` is zero. -/
theorem hi_zero {m : Mem} {B : Addr} {d x : Nat} (h : m.readW (B + BitVec.ofNat 64 d) 64 = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 32) : m.readW (B + BitVec.ofNat 64 (d + 4)) 32 = 0 := by
  rw [Proof.Ffdh.X86.KeyInit.readW64_split, Offset.add_add] at h
  have := congrArg BitVec.toNat h
  rw [pair32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  apply BitVec.eq_of_toNat_eq
  have := (m.readW (B + BitVec.ofNat 64 d) 32).isLt
  have h2 : (m.readW (B + BitVec.ofNat 64 (d + 4)) 32).toNat * 2 ^ 32 < 2 ^ 32 := by omega
  show _ = 0
  omega

theorem limit_lt (L : Nat) (eB : List Byte) (hL : L ≤ 512) : limitOf L eB < 2 ^ 32 := by
  unfold limitOf primeLimit; split <;> omega

/-- The next prime's search, of the phase `phase`, from all its counted candidates. -/
theorem nextPrime_ok {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (phase : KeyPhase)
    (hf : GenFrame p o used st s) :
    WP isa (.block (nextPrime (phaseWord phase))) s fun t =>
      GenFrame p o used ⟨st.left, phase, limitOf p.L p.eB⟩ t ∧ t.gpr .ebx = 4 ∧
        Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 0, 36⟩] s.mem t.mem ∧
        word t.mem p.stp 24 = word s.mem p.stp 24 ∧ Keep [.eax, .ecx, .ebx] s t := by
  have hb := hf.toGenBase
  have hi := hb.input
  have hs := hi.sBound'
  have hv := hi.len_valid
  have hlim := limit_lt p.L p.eB (by omega)
  have hph : phaseWord phase < 2 ^ 32 := by unfold phaseWord; split <;> decide
  refine WP.mono (WP.blockKeep [.eax, .ecx, .ebx] (Q := fun t =>
      t.gpr .ebx = 4 ∧
      (t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 0) 32 = BitVec.ofNat 32 (limitOf p.L p.eB) ∧
        t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 4) 32 = 0 ∧
        t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 32 = BitVec.ofNat 32 (phaseWord phase) ∧
        t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 36) 32 =
          s.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 36) 32) ∧
      Frame [⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 0, 8⟩, ⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 32, 4⟩]
        s.mem t.mem) ?_ (by rfl))
    fun t ⟨⟨hbx, ⟨h0, h4, h32, h36⟩, fr⟩, k, sy⟩ => ?_
  · simp only [nextPrime, VG.Impl.RsaKeyGen.X86.Generate.st, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 7) (d := 48) rfl, hb.arg_in (i := 7) (by decide),
      hb.arg_val (i := 7) (by decide), st_ea hi (d := 0) (by decide), st_ea hi (d := 4) (by decide),
      st_ea hi (d := 32) (by decide), hb.st_inW (d := 0) (n := 4) (by decide),
      hb.st_inW (d := 4) (n := 4) (by decide), hb.st_inW (d := 32) (n := 4) (by decide), hf.edi]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp (disch := decide) only [rdS, rdN]
    · simp (disch := decide) only [rdS, rdN]
    · simp only [rdS]
    · simp (disch := decide) only [rdN]
    · refine Frame.writeW ?_ (r := ⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 32, 4⟩) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))
      refine Frame.writeW ?_ (r := ⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 0, 8⟩) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))
      refine Frame.writeW ?_ (r := ⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 0, 8⟩) (by simp) _
        (Offset.contains _ (by decide) (by decide) (by decide))
      exact Frame.refl _ _
  have hst := hf.state
  rw [← hi.stp_eq] at fr h0 h4 h32 h36
  have far (e : Nat) (he : e + 8 ≤ 32 ∧ 8 ≤ e ∨ 40 ≤ e ∧ e + 8 ≤ 56) : word t.mem p.stp e = word s.mem p.stp e :=
    word_keep fr fun r hr => by
      have := p.stp.isLt
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have hph1 : phaseWord st.phase < 2 ^ 32 := by unfold phaseWord; split <;> decide
  have h36' := hi_zero (d := 32) hst.phase hph1
  have hst' : StateOk p ⟨st.left, phase, limitOf p.L p.eB⟩ t.mem := by
    refine ⟨?_, (far 8 (by omega)).trans hst.len, (far 16 (by omega)).trans hst.cap, ?_,
      (far 40 (by omega)).trans hst.left, ?_, Nat.le_refl _, hst.left_lt⟩
    · exact (word_halves (d := 0) h0 h4).trans (zero_app hlim)
    · exact (word_halves (d := 32) h32 (h36.trans h36')).trans (zero_app hph)
    · rw [← hst.e]
      exact bytes_keep (R := ⟨p.stp.setWidth 64 + BitVec.ofNat 64 48, 8⟩) fr (fun r hr => by
        have := p.stp.isLt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inr (by decide)) (by omega) (by omega))
        (show 8 ≤ 2 ^ 64 by decide)
  have fr' : Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 0, 36⟩] s.mem t.mem := fr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, by
        rw [show p.stp.setWidth 64 + BitVec.ofNat 64 32 = p.stp.setWidth 64 + BitVec.ofNat 64 0 + BitVec.ofNat 64 32 by
          rw [BitVec.add_zero]]
        exact Offset.sub_base _ (by decide)⟩
  exact ⟨hf.stateWrite k (by decide) sy (by decide) fr' hst', hbx, fr', far 24 (by omega), k⟩

/-- The 64-bit word less 1, of its halves. -/
theorem dec64 (hi lo : BitVec 32) (h1 : 1 ≤ (hi ++ lo).toNat) :
    (hi - 0 - (BitVec.ofBool (decide (lo.toNat < (1 : BitVec 32).toNat))).setWidth 32) ++ (lo - 1) =
      BitVec.ofNat 64 ((hi ++ lo).toNat - 1) := by
  rw [pair32] at h1 ⊢
  apply BitVec.eq_of_toNat_eq
  rw [pair32, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  have hl := lo.isLt
  have hh := hi.isLt
  by_cases h0 : lo.toNat = 0
  · have hh1 : 1 ≤ hi.toNat := by omega
    simp only [h0, Nat.lt_one_iff, decide_true, BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofBool, Bool.toNat_true, show (0 : BitVec 32).toNat = 0 from rfl,
      show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  · simp only [show ¬ lo.toNat < 1 by omega, decide_false, BitVec.toNat_sub,
      BitVec.toNat_setWidth, BitVec.toNat_ofBool, Bool.toNat_false, show (0 : BitVec 32).toNat = 0 from rfl,
      show (1 : BitVec 32).toNat = 1 from rfl]
    omega

/-- One generation fewer: the 64-bit word of the generations left, less 1. -/
theorem dec_ok {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (hf : GenFrame p o used st s)
    (hax : s.gpr .eax = arg o 7) (hl : 1 ≤ st.left) :
    WP isa (.block [.mov .ecx (.mem (VG.Impl.RsaKeyGen.X86.Generate.st 40)), .alu .sub .ecx (.imm 1),
      .store (VG.Impl.RsaKeyGen.X86.Generate.st 40) .ecx, .mov .ecx (.mem (VG.Impl.RsaKeyGen.X86.Generate.st 44)),
      .alu .sbb .ecx (.imm 0), .store (VG.Impl.RsaKeyGen.X86.Generate.st 44) .ecx]) s fun t =>
      GenFrame p o used ⟨st.left - 1, st.phase, st.remaining⟩ t ∧
        Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 40, 8⟩] s.mem t.mem ∧ Keep [.ecx] s t := by
  have hb := hf.toGenBase
  have hi := hb.input
  have hs := hi.sBound'
  refine WP.mono (WP.blockKeep [.ecx] (Q := fun t =>
      (t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 40) 32 =
          s.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 40) 32 - 1 ∧
        t.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 44) 32 =
          s.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 44) 32 - 0 -
            (BitVec.ofBool (decide ((s.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 40) 32).toNat <
              (1 : BitVec 32).toNat))).setWidth 32) ∧
      Frame [⟨(arg o 7).setWidth 64 + BitVec.ofNat 64 40, 8⟩] s.mem t.mem) ?_ (by rfl))
    fun t ⟨⟨⟨h40, h44⟩, fr⟩, k, sy⟩ => ?_
  · simp only [VG.Impl.RsaKeyGen.X86.Generate.st]
    xrun [State.ea, at_, hax, st_ea hi (d := 40) (by decide), st_ea hi (d := 44) (by decide),
      hb.st_inW (d := 40) (n := 4) (by decide), hb.st_inW (d := 44) (n := 4) (by decide),
      hb.st_in (d := 40) (n := 4) (by decide), hb.st_in (d := 44) (n := 4) (by decide)]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp (disch := decide) only [rdS, rdN]
    · simp (disch := decide) only [rdS, rdN]
    · iterate 2 (refine st_slot ?_ ?hd _; case hd => exact ⟨by decide, by decide, by decide⟩)
      exact Frame.refl _ _
  have hst := hf.state
  rw [← hi.stp_eq] at fr h40 h44
  have hw := hst.left
  have hlt := hst.left_lt
  simp only [word] at hw
  rw [Proof.Ffdh.X86.KeyInit.readW64_split, Offset.add_add] at hw
  simp only [Nat.reduceAdd] at hw
  have hv : (s.mem.readW (p.stp.setWidth 64 + BitVec.ofNat 64 44) 32 ++
      s.mem.readW (p.stp.setWidth 64 + BitVec.ofNat 64 40) 32).toNat = st.left := by
    rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have far (e : Nat) (he : e + 8 ≤ 40 ∨ 48 ≤ e) (he' : e + 8 ≤ 56) : word t.mem p.stp e = word s.mem p.stp e :=
    word_apart fr he ⟨by decide, he'⟩
  have hst' : StateOk p ⟨st.left - 1, st.phase, st.remaining⟩ t.mem := by
    refine ⟨(far 0 (by omega) (by omega)).trans hst.remaining, (far 8 (by omega) (by omega)).trans hst.len,
      (far 16 (by omega) (by omega)).trans hst.cap, (far 32 (by omega) (by omega)).trans hst.phase, ?_,
      by rw [e_apart fr (by decide)]; exact hst.e, hst.remaining_le, by show st.left - 1 < 2 ^ 64; omega⟩
    show t.mem.readW (p.stp.setWidth 64 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (st.left - 1)
    rw [word_halves (d := 40) h40 h44, dec64 _ _ (by omega), hv]
  exact ⟨hf.stateWrite k (by decide) sy (by decide) fr hst', fr, k⟩

/-- `sbb r, r`'s mask after a comparison. -/
abbrev msk (c : Bool) : BitVec 32 := 0#32 - (BitVec.ofBool c).setWidth 32

theorem left_flag (hi lo : BitVec 32) :
    (!((msk (decide (hi.toNat < (1 : BitVec 32).toNat)) &&& msk (decide (lo.toNat < (2 : BitVec 32).toNat)) &&&
        (msk (decide (hi.toNat < (1 : BitVec 32).toNat)) &&& msk (decide (lo.toNat < (2 : BitVec 32).toNat)))) ==
          0)) = decide ((hi ++ lo).toNat < 2) := by
  rw [pair32, show (1 : BitVec 32).toNat = 1 from rfl, show (2 : BitVec 32).toNat = 2 from rfl]
  by_cases ha : hi.toNat < 1 <;> by_cases hb : lo.toNat < 2
  · rw [decide_eq_true ha, decide_eq_true hb, decide_eq_true (show hi.toNat * 2 ^ 32 + lo.toNat < 2 by omega)]
    decide
  · rw [decide_eq_true ha, decide_eq_false hb, decide_eq_false (show ¬ hi.toNat * 2 ^ 32 + lo.toNat < 2 by omega)]
    decide
  · rw [decide_eq_false ha, decide_eq_true hb, decide_eq_false (show ¬ hi.toNat * 2 ^ 32 + lo.toNat < 2 by omega)]
    decide
  · rw [decide_eq_false ha, decide_eq_false hb, decide_eq_false (show ¬ hi.toNat * 2 ^ 32 + lo.toNat < 2 by omega)]
    decide

/-- Whether at least two generations are left: `ne` when fewer. -/
theorem left_test {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (hf : GenFrame p o used st s) :
    WP isa (.block [.mov .eax (.mem (param 0 7)), .mov .ecx (.mem (VG.Impl.RsaKeyGen.X86.Generate.st 44)),
      .alu .cmp .ecx (.imm 1), .alu .sbb .ecx (.reg .ecx), .mov .edx (.mem (VG.Impl.RsaKeyGen.X86.Generate.st 40)),
      .alu .cmp .edx (.imm 2), .alu .sbb .edx (.reg .edx), .alu .and .ecx (.reg .edx), .alu .test .ecx (.reg .ecx)])
      s fun t =>
      (eval .ne t = some (decide (st.left < 2)) ∧ t.gpr .eax = arg o 7 ∧ t.mem = s.mem) ∧
        Keep [.eax, .ecx, .edx] s t ∧ t.syms = s.syms := by
  have hb := hf.toGenBase
  have hi := hb.input
  refine WP.blockKeep [.eax, .ecx, .edx] ?_ (by rfl)
  simp only [VG.Impl.RsaKeyGen.X86.Generate.st, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 7) (d := 48) rfl, hb.arg_in (i := 7) (by decide),
    hb.arg_val (i := 7) (by decide), st_ea hi (d := 40) (by decide), st_ea hi (d := 44) (by decide),
    hb.st_in (d := 40) (n := 4) (by decide), hb.st_in (d := 44) (n := 4) (by decide), eval]
  have hw := hf.state.left
  have hlt := hf.state.left_lt
  simp only [word] at hw
  rw [Proof.Ffdh.X86.KeyInit.readW64_split, Offset.add_add] at hw
  simp only [Nat.reduceAdd] at hw
  have hv : (s.mem.readW (p.stp.setWidth 64 + BitVec.ofNat 64 44) 32 ++
      s.mem.readW (p.stp.setWidth 64 + BitVec.ofNat 64 40) 32).toNat = st.left := by
    rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [← hi.stp_eq, ← hv]
  exact left_flag _ _

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The controller's tests and the ends of the key search (i686)

Comparisons that keep the state (`cmp_ok`), the phase's test, the key's
buffer as the key's outputs, and the end of the key search with a status
(`fail_done`, `finish_done`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch (primeOf limitOf)

theorem sub_beq_zero32 (a b : BitVec 32) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have := congrArg (· + b) h
    simp only [BitVec.sub_add_cancel] at this
    rw [this]; exact BitVec.zero_add b
  · intro h; rw [h, BitVec.sub_self]; rfl

/-- A comparison with an immediate: the flags, and the state kept. -/
theorem cmp_ok {s : State} {r : Reg} {x : BitVec 32} (hx : s.gpr r = x) (k : BitVec 32) :
    WP isa (.block [.alu .cmp r (.imm k)]) s fun t =>
      (eval .e t = some (x == k) ∧ t.mem = s.mem) ∧ Keep [] s t ∧ t.syms = s.syms := by
  refine WP.mono (WP.blockKeep [r] (Q := fun t =>
      eval .e t = some (x == k) ∧ t.mem = s.mem ∧ t.gpr r = s.gpr r) ?_ (by cases r <;> rfl))
    fun t ⟨⟨h1, h2, h3⟩, k', sy⟩ => ⟨⟨h1, h2⟩, ⟨fun q _ => ?_, k'.2⟩, sy⟩
  · xrun [hx, eval]
    simp only [sub_beq_zero32]
  · by_cases hq : q = r
    · subst hq; exact h3
    · exact k'.gpr (by simpa using hq)

/-- A 32-bit value against an immediate, as numbers. -/
theorem beq_nat {x : BitVec 32} {n k : Nat} (hx : x.toNat = n) (hk : k < 2 ^ 32) :
    (x == BitVec.ofNat 32 k) = decide (n = k) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, hx]

theorem GenFrame.same {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s)
    (k : Keep [] s t) (sy : t.syms = s.syms) (hm : t.mem = s.mem) : GenFrame p o used st t :=
  ⟨h.toGenBase.step k (by decide) sy hm, h.used_le, (k.gpr (by decide)).trans h.ebp,
    (k.gpr (by decide)).trans h.esi, (k.gpr (by decide)).trans h.edi, by rw [hm]; exact h.random,
    by rw [hm]; exact h.state⟩

theorem Mid.same {p : GenPublic} {o u v : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}
    (h : Mid p o final used st u) (k : Keep [] u v) (sy : v.syms = u.syms) (hm : v.mem = u.mem) :
    Mid p o final used st v := by
  refine ⟨h.frame.same k sy hm, (k.gpr (by decide)).trans h.ebx, by rw [k.gpr (by decide)]; exact h.status,
    (k.gpr (by decide)).trans h.ecx, h.final, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hm]
  exacts [h.low, h.slot4, h.slot5, h.high, h.req]

/-- The key's buffer: the low four slots, `p`'s, `q`'s and the high three. -/
theorem key_bytes (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m (p.kp.setWidth 64) (9 * p.L) = Spec.Rsa.bytesAt m (p.kp.setWidth 64) (4 * p.L) ++
      Spec.Rsa.bytesAt m (p.slot 4) p.L ++ Spec.Rsa.bytesAt m (p.slot 5) p.L ++
      Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) := by
  rw [show 9 * p.L = 4 * p.L + p.L + p.L + 3 * p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show 4 * p.L + p.L = 5 * p.L by omega, show 5 * p.L + p.L = 6 * p.L by omega]

/-- The key's buffer, as the key's outputs. -/
theorem key_outs (p : GenPublic) (m : Mem) :
    Spec.Rsa.bytesAt m (p.kp.setWidth 64) (9 * p.L) =
      ((keyOutsOf p).map fun o => Spec.Rsa.bytesAt m o.1 o.2).flatten := by
  simp only [keyOutsOf, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show 9 * p.L = 2 * p.L + 2 * p.L + p.L + p.L + p.L + p.L + p.L by omega]
  rw [bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add,
    show 2 * p.L + 2 * p.L = 4 * p.L by omega, show 4 * p.L + p.L = 5 * p.L by omega,
    show 5 * p.L + p.L = 6 * p.L by omega, show 6 * p.L + p.L = 7 * p.L by omega,
    show 7 * p.L + p.L = 8 * p.L by omega]
  simp only [List.append_assoc]

theorem low_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (p.kp.setWidth 64) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = 2 * p.L + 2 * p.L by omega, bytesAt_add, ← List.replicate_append_replicate]
  rw [h (p.kp.setWidth 64, 2 * p.L) (by simp [keyOutsOf]), h (p.slot 2, 2 * p.L) (by simp [keyOutsOf])]

theorem high_of_outs {p : GenPublic} {m : Mem}
    (h : ∀ o ∈ keyOutsOf p, Spec.Rsa.bytesAt m o.1 o.2 = List.replicate o.2 0) :
    Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  have e (j : Nat) : p.slot j + BitVec.ofNat 64 p.L = p.slot (j + 1) := by
    rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; rw [Nat.succ_mul]
  rw [show 4 * p.L = p.L + p.L + p.L + p.L by omega, bytesAt_add, bytesAt_add, bytesAt_add,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L + p.L) = p.slot 8 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega,
    show p.slot 5 + BitVec.ofNat 64 (p.L + p.L) = p.slot 7 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, e 5,
    h (p.slot 5, p.L) (by simp [keyOutsOf]), h (p.slot 6, p.L) (by simp [keyOutsOf]),
    h (p.slot 7, p.L) (by simp [keyOutsOf]), h (p.slot 8, p.L) (by simp [keyOutsOf]),
    List.replicate_append_replicate, List.replicate_append_replicate, List.replicate_append_replicate]

theorem key_far {p : GenPublic} {o : State} (hi : GenInput p o) {d n : Nat} (hd : d + n ≤ 56) :
    Region.Disjoint ⟨p.kp.setWidth 64, 9 * p.L⟩ ⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, n⟩ := by
  have A := hi.abi
  rw [← hi.kR_eq]
  exact A.ks.sub_right (by rw [hi.sR_eq]; exact Offset.sub_base _ hd)

/-- The key search ends with `status`, its buffer as it is. -/
theorem finish_done {p : GenPublic} {o s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p o u st s) (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩)
    (hr0 : st.remaining = 0) (hkey : Spec.Rsa.bytesAt s.mem (p.kp.setWidth 64) (9 * p.L) = keySearchBytes p.L final)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (.block (finishWith final.keyStatus)) s (GenDone p o final) := by
  have hi := h.input
  have hv := hi.len_valid
  refine WP.mono (finish_ok h hr0 final.keyStatus) fun t ⟨g, hbx, fr, _⟩ => ?_
  obtain ⟨req, hw, hr⟩ := hreq
  refine ⟨by rw [hu, hpr]; exact g, hbx, ?_, ⟨req, (word_apart fr (.inl (by decide)) ⟨by decide, by decide⟩).trans hw, hr⟩⟩
  rw [← hkey]
  exact bytes_keep (R := ⟨p.kp.setWidth 64, 9 * p.L⟩) fr (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact key_far hi (by decide)) (show 9 * p.L ≤ 2 ^ 64 by omega)

/-- `fail status`: zeros at the key's buffer, and the key search ended with
`final`. -/
theorem fail_done {p : GenPublic} {o s : State} {u : Nat} {st : KeyProgress} {final : KeySearchResult}
    (h : GenFrame p o u st s) (hu : final.used = u) (hpr : final.progress = ⟨0, .p, 0⟩)
    (hr0 : st.remaining = 0) (hz : keySearchBytes p.L final = List.replicate (9 * p.L) 0)
    (hreq : ∃ requested, word s.mem p.stp 24 = BitVec.ofNat 64 requested ∧
      final.Requests (primeEntropy p.L) requested) :
    WP isa (fail final.keyStatus) s (GenDone p o final) := by
  have hi := h.input
  have A := hi.abi
  unfold fail
  refine WP.seq (WP.mono (clearAll_ok h) fun w ⟨g, fr, z, _⟩ => ?_)
  obtain ⟨req, hw, hr⟩ := hreq
  refine finish_done g hu hpr hr0 (z.trans hz.symm) ⟨req, ?_, hr⟩
  refine (word_keep fr fun r hr => ?_).trans hw
  obtain rfl := List.mem_singleton.mp hr
  rw [hi.kR_eq]; exact (key_far hi (by decide)).symm

end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The ways a prime's search ends (i686)

After a search: the key search asks for more entropy, ends exhausted, or
goes on to the next generation or to `q` after `p` (`Classified`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- How the key search goes on after the prime's search `r` from the progress
`st`: to the progress `st'`, with `e` this step's trace. -/
def NextPub (st : KeyProgress) (r : PrimeSearchResult) (st' : KeyProgress) (e : List Nat) : Prop :=
  (r.outcome = .exhausted ∧ st'.left = st.left - 1 ∧ st'.phase = .p ∧ e = primeEntry r) ∨
  (∃ c, r.outcome = .accepted c ∧ st.phase = .p ∧ st'.left = st.left ∧ phaseWord st'.phase = 1 ∧
    e = primeEntry r) ∨
  (∃ c pB, r.outcome = .accepted c ∧ st.phase = .q pB ∧ st'.left = st.left ∧ st'.phase = .p ∧
    e = primeEntry r ++ [1, 2])

/-- After a step that goes on: the loop state of the next prime's search, of
a lower measure, the state's request word 0. -/
structure Cont (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop where
  req : word t.mem p.stp 24 = BitVec.ofNat 64 0
  next : ∃ st' e, GenLive p o (used + (rOf p o used st).used) st' t ∧
    genMeasure p (used + (rOf p o used st).used) st' < genMeasure p used st ∧
    tailOf p o used st = (tailOf p o (used + (rOf p o used st).used) st').consume (rOf p o used st).used e ∧
    st'.remaining = limitOf p.L p.eB ∧ NextPub st (rOf p o used st) st' e
  final : ∃ tr, final = (tailOf p o used st).consume used tr

/-- Whether the key search goes on after the prime's search from `st`. -/
def ContSpec (p : GenPublic) (o : State) (used : Nat) (st : KeyProgress) : Prop :=
  ((rOf p o used st).outcome = .exhausted ∧ ¬st.left < 2) ∨
  (∃ c, (rOf p o used st).outcome = .accepted c ∧ (rOf p o used st).used ≠ 0 ∧
    (st.phase = .p ∨ ∃ pB, st.phase = .q pB ∧ keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB)
      (Spec.Rsa.os2ip pB) (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) = .inr ()))

/-- After a step: the next prime's search, or the key search ended with
`final`. -/
def Classified (p : GenPublic) (o : State) (final : KeySearchResult) (used : Nat) (st : KeyProgress)
    (t : State) : Prop :=
  (ContSpec p o used st ∧ Cont p o final used st t) ∨ (¬ContSpec p o used st ∧ GenDone p o final t)

theorem GenFrame.keepRegs {p : GenPublic} {o s t : State} {used : Nat} {st : KeyProgress}
    (h : GenFrame p o used st s) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ rs, r ≠ .esp ∧ r ≠ .ebp ∧ r ≠ .esi ∧ r ≠ .edi) (sy : t.syms = s.syms) (hm : t.mem = s.mem) :
    GenFrame p o used st t :=
  ⟨h.toGenBase.step k (fun h => (hrs _ h).1 rfl) sy hm, h.used_le, (k.gpr fun h => (hrs _ h).2.1 rfl).trans h.ebp,
    (k.gpr fun h => (hrs _ h).2.2.1 rfl).trans h.esi, (k.gpr fun h => (hrs _ h).2.2.2 rfl).trans h.edi,
    by rw [hm]; exact h.random, by rw [hm]; exact h.state⟩

theorem rOf_status (r : PrimeSearchResult) : r.status = r.outcome.status := rfl

theorem measure_lt (p : GenPublic) {used n : Nat} {st st' : KeyProgress} (h0 : 0 < n)
    (hn : used + n ≤ p.randLen) (hl : st'.left ≤ st.left) :
    genMeasure p (used + n) st' < genMeasure p used st := by
  unfold genMeasure
  have hmul : (p.randLen - (used + n) + 1) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hmul
  omega

theorem drop_lt {rest : List Byte} {n : Nat} (h0 : 0 < n) (hn : n ≤ rest.length) :
    (rest.drop n).length < rest.length := by
  rw [List.length_drop]; omega

theorem high_parts {p : GenPublic} {m : Mem}
    (h5 : Spec.Rsa.bytesAt m (p.slot 5) p.L = List.replicate p.L 0)
    (h6 : Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0) :
    Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
  rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
    show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
      rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, h5, h6,
    ← List.replicate_append_replicate]

/-- The key's buffer apart from stores to the state's words. -/
theorem kb_keep {p : GenPublic} {o : State} (hi : GenInput p o) {m m' : Mem} {d n : Nat} (hd : d + n ≤ 56)
    (fr : Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 d, n⟩] m m') {a : Addr} {len : Nat}
    (ha : Region.Sub ⟨a, len⟩ ⟨p.kp.setWidth 64, 9 * p.L⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' a len = Spec.Rsa.bytesAt m a len :=
  bytes_keep (R := ⟨a, len⟩) fr (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact (key_far hi hd).sub_left ha) hl

/-- The key's buffer for the next prime's search, through the stores to the
state. -/
theorem keyOk_next {p : GenPublic} {o : State} (hi : GenInput p o) {st : KeyProgress} {m m' : Mem}
    (fr : Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 0, 36⟩] m m')
    (hlow : Spec.Rsa.bytesAt m (p.kp.setWidth 64) (4 * p.L) = List.replicate (4 * p.L) 0)
    (h5 : Spec.Rsa.bytesAt m (p.slot 5) p.L = List.replicate p.L 0)
    (h6 : Spec.Rsa.bytesAt m (p.slot 6) (3 * p.L) = List.replicate (3 * p.L) 0)
    (hother : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt m (p.slot 4) p.L = pB) : KeyOk p st m' := by
  have hv := hi.len_valid
  have hhigh : Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0 := by
    rw [show 4 * p.L = p.L + 3 * p.L by omega, bytesAt_add,
      show p.slot 5 + BitVec.ofNat 64 p.L = p.slot 6 by
        rw [GenPublic.slot, GenPublic.slot, Offset.add_add]; congr 2; omega, h5, h6,
      ← List.replicate_append_replicate]
  exact KeyOk.frame ⟨hlow, hhigh, hother⟩ hi.kBound' (key_far hi (by decide)).symm fr

theorem keyOk_nextH {p : GenPublic} {o : State} (hi : GenInput p o) {st : KeyProgress} {m m' : Mem}
    (fr : Frame [⟨p.stp.setWidth 64 + BitVec.ofNat 64 0, 36⟩] m m')
    (hlow : Spec.Rsa.bytesAt m (p.kp.setWidth 64) (4 * p.L) = List.replicate (4 * p.L) 0)
    (hhigh : Spec.Rsa.bytesAt m (p.slot 5) (4 * p.L) = List.replicate (4 * p.L) 0)
    (hother : ∀ pB, st.phase = .q pB → Spec.Rsa.bytesAt m (p.slot 4) p.L = pB) : KeyOk p st m' :=
  KeyOk.frame ⟨hlow, hhigh, hother⟩ hi.kBound' (key_far hi (by decide)).symm fr

/-- The phase's test: `e` for `p`'s search. -/
theorem phase_test {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (hf : GenFrame p o used st s) :
    WP isa (.block [.mov .eax (.mem (param 0 7)), .mov .ecx (.mem (VG.Impl.RsaKeyGen.X86.Generate.st 32)),
      .alu .cmp .ecx (.imm 0)]) s fun t =>
      (eval .e t = some (decide (phaseWord st.phase = 0)) ∧ t.mem = s.mem) ∧ Keep [.eax, .ecx] s t ∧
        t.syms = s.syms := by
  have hb := hf.toGenBase
  have hi := hb.input
  have r32 : s.mem.readW ((arg o 7).setWidth 64 + BitVec.ofNat 64 32) 32 = BitVec.ofNat 32 (phaseWord st.phase) := by
    rw [← hi.stp_eq]; exact low_half hf.state.phase
  have hph : phaseWord st.phase < 2 ^ 32 := by unfold phaseWord; split <;> decide
  refine WP.blockKeep [.eax, .ecx] ?_ (by rfl)
  simp only [VG.Impl.RsaKeyGen.X86.Generate.st, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 7) (d := 48) rfl, hb.arg_in (i := 7) (by decide),
    hb.arg_val (i := 7) (by decide), st_ea hi (d := 32) (by decide), hb.st_in (d := 32) (n := 4) (by decide), r32,
    eval, sub_beq_zero32]
  exact beq_nat (BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt hph) (by decide)

section

variable {p : GenPublic} {o u : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

/-- The search asked for more entropy: so does the key search. -/
theorem classify_entropy (hm : Mid p o final used st u) {k a : Nat}
    (ho : (rOf p o used st).outcome = .entropy k a) :
    WP isa (.block [.mov .ebx (.imm 0)]) u (Classified p o final used st) := by
  have hv := hm.frame.input.len_valid
  have hrem : (rOf p o used st).remaining = k := by simp only [PrimeSearchResult.remaining, ho]
  have hframe := hm.frame
  rw [hrem] at hframe
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_entropy (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho
  have hfinal : final = ⟨.entropy ⟨st.left, st.phase, k⟩ a, used + (rOf p o used st).used,
      tr ++ primeEntry (rOf p o used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  have nc : ¬ContSpec p o used st := by
    rintro (⟨h, -⟩ | ⟨c, h, -⟩) <;> rw [ho] at h <;> cases h
  refine WP.mono (WP.blockKeep [.ebx] (Q := fun t => t.gpr .ebx = 0 ∧ t.mem = u.mem) (by xrun) (by rfl))
    fun t ⟨⟨hbx, htm⟩, k', sy⟩ => Or.inr ⟨nc, ?_⟩
  have hg := hframe.keepRegs k' (by decide) sy htm
  obtain ⟨req, hw, hr⟩ := hm.req
  subst hfinal
  refine ⟨hg, hbx, ?_, ⟨req, by rw [htm]; exact hw, ?_⟩⟩
  · rw [htm, key_bytes, hm.low, hm.slot4, hm.slot5, hm.high]
    have hout : outBytes p.L (rOf p o used st) = List.replicate p.L 0 := by simp only [outBytes, ho]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p =>
      simp only [hout, keySearchBytes, List.replicate_append_replicate]
      congr 1; omega
    | q pB =>
      simp only [hout, keySearchBytes, List.append_assoc, List.replicate_append_replicate]
      congr 3; omega
  · simp only [Spec.Entropy.Result.Requests, ho] at hr ⊢
    exact hr

/-- The search was exhausted, and so is the key search: its last generation. -/
theorem classify_last (hm : Mid p o final used st u) (ho : (rOf p o used st).outcome = .exhausted)
    (hl : st.left < 2) {w : State}
    (hw : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ w)
    (hmem : w.mem = u.mem) : WP isa (fail 3) w (GenDone p o final) := by
  have hrem : (rOf p o used st).remaining = 0 := by simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_exhausted_last (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho (by omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p o used st).used, tr ++ primeEntry (rOf p o used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw', hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done (final := ⟨.exhausted, used + (rOf p o used st).used, tr ++ primeEntry (rOf p o used st)⟩)
    hw rfl rfl hrem rfl ⟨req, by rw [hmem]; exact hw', by rw [hr0]; rfl⟩

/-- A prime accepted having read nothing: the key search is exhausted. -/
theorem classify_none (hm : Mid p o final used st u) {c : Nat}
    (ho : (rOf p o used st).outcome = .accepted c) (h0 : (rOf p o used st).used = 0) {w : State}
    (hw : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ w)
    (hmem : w.mem = u.mem) : WP isa (fail 3) w (GenDone p o final) := by
  have hrem : (rOf p o used st).remaining = 0 := by simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨tr, hfin⟩ := hm.final
  have hks := ks_accepted_none (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho
    (by show ¬(List.drop (rOf p o used st).used _).length < _; rw [h0, List.drop_zero]; omega)
  have hfinal : final = ⟨.exhausted, used + (rOf p o used st).used, tr ++ primeEntry (rOf p o used st)⟩ := by
    rw [hfin, tailOf, hks]; rfl
  obtain ⟨req, hw', hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hfinal
  exact fail_done (final := ⟨.exhausted, used + (rOf p o used st).used, tr ++ primeEntry (rOf p o used st)⟩)
    hw rfl rfl hrem rfl ⟨req, by rw [hmem]; exact hw', by rw [hr0]; rfl⟩

/-- The search was exhausted: the next generation, from `p`. -/
theorem classify_next (hm : Mid p o final used st u) (ho : (rOf p o used st).outcome = .exhausted)
    (hl : ¬st.left < 2) {w : State}
    (hw : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ w)
    (hmem : w.mem = u.mem) (hax : w.gpr .eax = arg o 7) :
    WP isa (.block (([.mov .ecx (.mem (VG.Impl.RsaKeyGen.X86.Generate.st 40)), .alu .sub .ecx (.imm 1),
      .store (VG.Impl.RsaKeyGen.X86.Generate.st 40) .ecx, .mov .ecx (.mem (VG.Impl.RsaKeyGen.X86.Generate.st 44)),
      .alu .sbb .ecx (.imm 0), .store (VG.Impl.RsaKeyGen.X86.Generate.st 44) .ecx] : List Instr) ++ nextPrime 0)) w
      (Classified p o final used st) := by
  have hi := hm.frame.input
  have hv := hi.len_valid
  have hle := hm.frame.used_le
  have hks := ks_exhausted_next (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho (by omega)
  have hout : outBytes p.L (rOf p o used st) = List.replicate p.L 0 := by simp only [outBytes, ho]
  have h5 : Spec.Rsa.bytesAt u.mem (p.slot 5) p.L = List.replicate p.L 0 := by
    rw [hm.slot5]
    obtain ⟨left, phase, remaining⟩ := st
    cases phase with
    | p => rfl
    | q pB => exact hout
  refine WP.block_append (WP.mono (dec_ok hw hax (by show 1 ≤ st.left; omega)) fun t1 ⟨g1, fr1, _⟩ => ?_)
  refine WP.mono (nextPrime_ok .p g1) fun t ⟨g, hbx, fr, w24, _⟩ => Or.inl ⟨.inl ⟨ho, hl⟩, ?_⟩
  have tk {a : Addr} {len : Nat} (ha : Region.Sub ⟨a, len⟩ ⟨p.kp.setWidth 64, 9 * p.L⟩) (hl : len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt t1.mem a len = Spec.Rsa.bytesAt u.mem a len := by
    rw [kb_keep hi (by decide) fr1 ha hl, hmem]
  have hkey : KeyOk p ⟨st.left - 1, .p, limitOf p.L p.eB⟩ t.mem := by
    refine keyOk_next hi fr ?_ ?_ ?_ (fun _ h => by cases h)
    · rw [tk (Region.sub_prefix (by omega)) (by omega)]; exact hm.low
    · rw [tk (Offset.sub_base _ (by omega)) (by omega)]; exact h5
    · rw [tk (Offset.sub_base _ (by omega)) (by omega)]; exact hm.high
  have hreq0 : word t.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [w24, word_apart fr1 (.inl (by decide)) ⟨by decide, by decide⟩, hmem, hw', this]
  refine ⟨hreq0, ⟨_, primeEntry (rOf p o used st), ⟨g, hbx, hkey⟩, ?_, ?_, rfl, .inl ⟨ho, rfl, rfl, rfl⟩⟩, hm.final⟩
  · unfold genMeasure
    dsimp only
    have hmul : (p.randLen - (used + (rOf p o used st).used)) * 2 ^ 64 ≤ (p.randLen - used) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [tailOf, hks, tailOf, List.drop_drop]

/-- `p` accepted: `q` next. -/
theorem classify_p (hm : Mid p o final used st u) {c : Nat}
    (ho : (rOf p o used st).outcome = .accepted c) (hpos : 0 < (rOf p o used st).used)
    (hph : st.phase = .p) {w : State}
    (hw : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ w)
    (hmem : w.mem = u.mem) :
    WP isa (.block (nextPrime 1)) w (Classified p o final used st) := by
  have hi := hm.frame.input
  have hv := hi.len_valid
  have hle := hm.frame.used_le
  have hrest : (rOf p o used st).used ≤ ((genRand o).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hks := ks_accepted_p (L := p.L) (eB := p.eB) (st := st) (rand := (genRand o).drop used) ho
    (drop_lt hpos hrest) hph
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs4
  refine WP.mono (nextPrime_ok (.q (Spec.Rsa.i2osp c p.L)) hw) fun t ⟨g, hbx, fr, w24, _⟩ =>
    Or.inl ⟨.inr ⟨c, ho, by omega, .inl hph⟩, ?_⟩
  have hkey : KeyOk p ⟨st.left, .q (Spec.Rsa.i2osp c p.L), limitOf p.L p.eB⟩ t.mem := by
    refine keyOk_next hi fr ?_ ?_ ?_ (fun pB h => ?_)
    · rw [hmem]; exact hm.low
    · rw [hmem]; exact hs5
    · rw [hmem]; exact hm.high
    · cases h; rw [hmem]; exact hs4
  have hreq0 : word t.mem p.stp 24 = BitVec.ofNat 64 0 := by
    obtain ⟨req, hw', hr'⟩ := hm.req
    have : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr'
    rw [w24, hmem, hw', this]
  refine ⟨hreq0, ⟨_, primeEntry (rOf p o used st), ⟨g, hbx, hkey⟩, measure_lt p hpos hm.frame.used_le
    (Nat.le_refl _), ?_, rfl, .inr (.inl ⟨c, ho, hph, rfl, rfl, rfl⟩)⟩, hm.final⟩
  rw [tailOf, hks, tailOf, List.drop_drop]

/-- After `q`: the key. -/
theorem classify_key (key : KeyImpl) (hm : Mid p o final used st u) {c : Nat} {pB : List Byte}
    (ho : (rOf p o used st).outcome = .accepted c) (hpos : 0 < (rOf p o used st).used)
    (hph : st.phase = .q pB) {w : State}
    (hw : GenFrame p o (used + (rOf p o used st).used) ⟨st.left, st.phase, (rOf p o used st).remaining⟩ w)
    (hmem : w.mem = u.mem) :
    WP isa (.seq (keyRun key.call) afterKey) w (Classified p o final used st) := by
  have hi := hm.frame.input
  have A := hi.abi
  have hv := hi.len_valid
  obtain ⟨tr, hfin⟩ := hm.final
  have hle := hm.frame.used_le
  have hrest : (rOf p o used st).used ≤ ((genRand o).drop used).length := by
    rw [List.length_drop, genRand_length hm.frame]; omega
  have hg := drop_lt hpos hrest
  have hs4 := hm.slot4
  have hs5 := hm.slot5
  rw [hph] at hs4 hs5
  simp only [outBytes, ho] at hs5
  have hrem : (rOf p o used st).remaining = 0 := by simp only [PrimeSearchResult.remaining, ho]
  obtain ⟨req, hw24, hr⟩ := hm.req
  have hr0 : req = 0 := by simpa only [Spec.Entropy.Result.Requests, ho] using hr
  subst hr0
  refine WP.seq (WP.mono (key_run key hw) fun v hk => ?_)
  have hkey : keyOf p w.mem = keyOp p.L p.eB pB (Spec.Rsa.i2osp c p.L) := by
    simp only [keyOf, hmem, hs4, hs5]
  have hstat := hk.status
  have hout := hk.out
  rw [hkey] at hstat hout
  have X : Region.Sub ⟨p.stp.setWidth 64 + BitVec.ofNat 64 24, 8⟩ (sR o) := by
    rw [hi.sR_eq]; exact Offset.sub_base _ (by decide)
  have hwv : word v.mem p.stp 24 = BitVec.ofNat 64 0 := by
    refine (word_keep hk.mem fun r hr => ?_).trans (by rw [hmem]; exact hw24)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact A.ks.symm.sub_left X
    · exact A.bs.symm.sub_left X
    · rw [← hi.low_eq]; exact A.lowS.symm.sub_left X
  unfold afterKey
  refine WP.seq (WP.mono (cmp_ok (r := .eax) rfl 1) fun x ⟨⟨he1, hmem1⟩, k1, sy1⟩ => ?_)
  have hgx := hk.frame.same k1 sy1 hmem1
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, beq_nat (k := 1) hstat (by decide)] at he1
  have hfin' : ∀ {res : KeySearchResult}, keySearch p.L p.eB st ((genRand o).drop used) = res →
      final = res.consume used tr := fun h => by rw [hfin, tailOf, h]
  cases hkf : keyFromPrimes (16 * p.L) (Spec.Rsa.os2ip p.eB) (Spec.Rsa.os2ip pB)
      (Spec.Rsa.os2ip (Spec.Rsa.i2osp c p.L)) with
  | inl res =>
    cases res with
    | ok kk =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .ok kk) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hout
      refine WP.ite true he1 (fun _ => ?_) (fun h => by cases h)
      have e : final.keyStatus = 1 := by rw [hks]; rfl
      rw [← e]
      refine WP.mono (finish_done (final := final) hgx (by rw [hks]; rfl) (by rw [hks]; rfl) hrem ?_
        ⟨0, by rw [hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr ⟨?_, h⟩
      · rw [hmem1, key_outs, hout, hks]
        simp only [keySearchBytes, Spec.Entropy.Result.consume, keyBytes, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.append_assoc]
      · rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
        · rw [ho] at h; cases h
        · rw [hph] at h'; cases h'
        · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
    | error fl =>
      have hks := hfin' (ks_accepted_key (L := p.L) (eB := p.eB) (res := .error fl) ho hg hph hkf)
      simp only [keyOp, hkf, keyStatus] at he1 hstat
      refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
      refine WP.seq (WP.mono (cmp_ok (r := .eax) rfl 2) fun y ⟨⟨he2, hmem2⟩, k2, sy2⟩ => ?_)
      rw [k1.gpr (by decide), show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, beq_nat (k := 2) hstat (by decide)] at he2
      have hgy := hgx.same k2 sy2 hmem2
      refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
      have e : final.keyStatus = 2 := by rw [hks]; rfl
      rw [← e]
      have nc : ¬ContSpec p o used st := by
        rintro (⟨h, -⟩ | ⟨c', h, -, h' | ⟨pB', h', hk'⟩⟩)
        · rw [ho] at h; cases h
        · rw [hph] at h'; cases h'
        · rw [ho] at h; cases h; rw [hph] at h'; cases h'; rw [hkf] at hk'; cases hk'
      exact WP.mono (fail_done (final := final) hgy (by rw [hks]; rfl) (by rw [hks]; rfl) hrem (by rw [hks]; rfl)
        ⟨0, by rw [hmem2, hmem1]; exact hwv, by rw [hks]; rfl⟩) fun _ h => Or.inr ⟨nc, h⟩
  | inr _ =>
    have hks := ks_accepted_small (L := p.L) (eB := p.eB) ho hg hph hkf
    simp only [keyOp, hkf, keyStatus] at he1 hstat hout
    refine WP.ite false he1 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp_ok (r := .eax) rfl 2) fun y ⟨⟨he2, hmem2⟩, k2, sy2⟩ => ?_)
    rw [k1.gpr (by decide), show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl, beq_nat (k := 2) hstat (by decide)] at he2
    have hgy := hgx.same k2 sy2 hmem2
    refine WP.ite true he2 (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (nextPrime_ok .p hgy) fun t ⟨g, hbx, fr, w24, _⟩ =>
      Or.inl ⟨.inr ⟨c, ho, by omega, .inr ⟨pB, hph, hkf⟩⟩, ?_⟩
    have hkey' : KeyOk p ⟨st.left, .p, limitOf p.L p.eB⟩ t.mem :=
      keyOk_nextH hi fr (by rw [hmem2, hmem1]; exact low_of_outs hout)
        (by rw [hmem2, hmem1]; exact high_of_outs hout) (fun _ h => by cases h)
    refine ⟨by rw [w24, hmem2, hmem1]; exact hwv, ⟨_, primeEntry (rOf p o used st) ++ [1, 2], ⟨g, hbx, hkey'⟩,
      measure_lt p hpos hle (Nat.le_refl _), ?_, rfl, .inr (.inr ⟨c, pB, ho, hph, rfl, rfl, rfl⟩)⟩, ⟨tr, hfin⟩⟩
    rw [tailOf, hks, tailOf, List.drop_drop]

end

/-- After the search: what it leaves, classified. -/
theorem classify_ok (key : KeyImpl) {p : GenPublic} {o s t : State} {final : KeySearchResult} {used : Nat}
    {st : KeyProgress} (hi : GenIter p o final used st s) (ha : AfterSearch p o used st s t) :
    WP isa (classify key.call) t (Classified p o final used st) := by
  unfold classify
  refine WP.seq (WP.mono (head_ok hi ha) fun u ⟨hm, hzf⟩ => ?_)
  have hu32 : (rOf p o used st).used < 2 ^ 32 := by
    have := hm.frame.used_le; have := hm.frame.input.randLen_lt; omega
  cases ho : (rOf p o used st).outcome with
  | entropy k a =>
    have hs : (rOf p o used st).status = 0 := by rw [rOf_status, ho]; rfl
    exact WP.ite true (by show u.zf = _; rw [hzf, hs]; rfl) (fun _ => classify_entropy hm ho) (fun h => by cases h)
  | exhausted =>
    have hs : (rOf p o used st).status = 3 := by rw [rOf_status, ho]; rfl
    refine WP.ite false (by show u.zf = _; rw [hzf, hs]; rfl) (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp_ok (r := .eax) rfl 3) fun v ⟨⟨he2, hmem⟩, k, sy⟩ => ?_)
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, beq_nat (k := 3) (hm.status.trans hs) (by decide)] at he2
    have hv := hm.same k sy hmem
    refine WP.ite true he2 (fun _ => ?_) (fun h => by cases h)
    unfold exhaustedGen
    refine WP.seq (WP.mono (left_test hv.frame) fun w ⟨⟨he3, hax, hmemw⟩, kw, syw⟩ => ?_)
    have hw := hv.frame.keepRegs kw (by decide) syw hmemw
    refine WP.ite (decide (st.left < 2)) he3 (fun hl => ?_) (fun hl => ?_)
    · refine WP.mono (classify_last hm ho (of_decide_eq_true hl) hw (hmemw.trans hmem)) fun _ h => Or.inr ⟨?_, h⟩
      rintro (⟨-, h⟩ | ⟨c, h, -⟩)
      · exact h (of_decide_eq_true hl)
      · rw [ho] at h; cases h
    · exact classify_next hm ho (of_decide_eq_false hl) hw (hmemw.trans hmem) hax
  | accepted c =>
    have hs : (rOf p o used st).status = 1 := by rw [rOf_status, ho]; rfl
    refine WP.ite false (by show u.zf = _; rw [hzf, hs]; rfl) (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp_ok (r := .eax) rfl 3) fun v ⟨⟨he2, hmem⟩, k, sy⟩ => ?_)
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, beq_nat (k := 3) (hm.status.trans hs) (by decide)] at he2
    have hv := hm.same k sy hmem
    refine WP.ite false he2 (fun h => by cases h) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp_ok (r := .ecx) rfl 0) fun w ⟨⟨he3, hmem3⟩, k3, sy3⟩ => ?_)
    rw [hv.ecx, show (0 : BitVec 32) = BitVec.ofNat 32 0 from rfl,
      beq_nat (k := 0) (BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt hu32) (by decide)] at he3
    have hw := hv.same k3 sy3 hmem3
    refine WP.ite (decide ((rOf p o used st).used = 0)) he3 (fun h0 => ?_) (fun h0 => ?_)
    · refine WP.mono (classify_none hm ho (of_decide_eq_true h0) hw.frame (hmem3.trans hmem)) fun _ h =>
        Or.inr ⟨?_, h⟩
      rintro (⟨h, -⟩ | ⟨c', -, hu, -⟩)
      · rw [ho] at h; cases h
      · exact hu (of_decide_eq_true h0)
    · have hpos : 0 < (rOf p o used st).used := by have := of_decide_eq_false h0; omega
      unfold accepted
      refine WP.seq (WP.mono (phase_test hw.frame) fun x ⟨⟨he4, hmem4⟩, k4, sy4⟩ => ?_)
      have hx := hw.frame.keepRegs k4 (by decide) sy4 hmem4
      have hxm : x.mem = u.mem := hmem4.trans (hmem3.trans hmem)
      obtain ⟨left, phase, remaining⟩ := st
      cases phase with
      | p => exact WP.ite true he4 (fun _ => classify_p hm ho hpos rfl hx hxm) (fun h => by cases h)
      | q pB => exact WP.ite false he4 (fun h => by cases h) (fun _ => classify_key key hm ho hpos rfl hx hxm)


end VG.Proof.RsaKeyGen.X86.Generate

/-! ## The controller's loop (i686)

Each iteration searches for the progress' prime, classifies the result, and
goes on while the status is 4, to a state of a lower measure; the loop ends
with the key search's result (`gen_loop`).
-/

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Spec.RsaKeyGen

section

variable {p : GenPublic} {o s t : State} {final : KeySearchResult} {used : Nat} {st : KeyProgress}

theorem GenLive.same (h : GenLive p o used st s) (k : Keep [] s t) (sy : t.syms = s.syms) (hm : t.mem = s.mem) :
    GenLive p o used st t :=
  ⟨h.toGenFrame.same k sy hm, (k.gpr (by decide)).trans h.ebx, by rw [hm]; exact h.key⟩

theorem GenDone.same (h : GenDone p o final s) (k : Keep [] s t) (sy : t.syms = s.syms) (hm : t.mem = s.mem) :
    GenDone p o final t := by
  obtain ⟨g, hb, hk, hr⟩ := h
  exact ⟨g.same k sy hm, (k.gpr (by decide)).trans hb, by rw [hm]; exact hk, by rw [hm]; exact hr⟩

theorem keyStatus_lt (r : KeySearchResult) : r.keyStatus < 4 := by
  unfold KeySearchResult.keyStatus
  split <;> decide

end

/-- An iteration: the search, its classification and the loop's test. -/
theorem gen_iteration (srch : Srch) (key : KeyImpl) {p : GenPublic} {o s : State} {final : KeySearchResult}
    {n : Nat} (h : GenInv p o final n s) :
    WP isa (iteration srch.call key.call) s fun t =>
      (eval .e t = some false ∧ GenDone p o final t) ∨
      (eval .e t = some true ∧ ∃ m < n, GenInv p o final m t) := by
  obtain ⟨used, st, rfl, hi⟩ := h
  unfold iteration
  refine WP.seq (WP.mono (search_run srch hi.1) fun t ha => ?_)
  refine WP.seq (WP.mono (classify_ok key hi ha) fun u hc => ?_)
  rcases hc with ⟨-, hct⟩ | ⟨-, hd⟩
  · obtain ⟨-, ⟨st', e, hl, hlt, htail, -, -⟩, ⟨tr, hfin⟩⟩ := hct
    refine WP.mono (cmp_ok (r := .ebx) rfl 4) fun x ⟨⟨he, hm⟩, k, sy⟩ =>
      Or.inr ⟨?_, _, hlt, _, st', rfl, hl.same k sy hm, tr ++ e, by
        rw [hfin, htail, Proof.RsaKeyGen.KeySearch.consume_consume]⟩
    rw [he, hl.ebx]; rfl
  · refine WP.mono (cmp_ok (r := .ebx) rfl 4) fun x ⟨⟨he, hm⟩, k, sy⟩ => Or.inl ⟨?_, hd.same k sy hm⟩
    have hlt := keyStatus_lt final
    rw [he, hd.2.1, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
      beq_nat (BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt (show final.keyStatus < 2 ^ 32 by omega)) (by decide)]
    simp only [Option.some.injEq, decide_eq_false_iff_not]
    omega

theorem gen_loop (srch : Srch) (key : KeyImpl) {p : GenPublic} {o s : State} {final : KeySearchResult} {n : Nat}
    (h : GenInv p o final n s) :
    WP isa (.loop (iteration srch.call key.call) .e) s (GenDone p o final) :=
  WP.loop (M := isa) (body := iteration srch.call key.call) (c := .e) (Q := GenDone p o final)
    (GenInv p o final) (fun _ _ h => gen_iteration srch key h) n s h

end VG.Proof.RsaKeyGen.X86.Generate
