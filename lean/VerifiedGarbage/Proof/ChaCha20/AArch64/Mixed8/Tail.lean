module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
public import VerifiedGarbage.Impl.ChaCha20.AArch64.Small
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `ChaCha20.AArch64.Small.Xor`, which this module and modules that import it used -/

section

/-! ### `ChaCha20.AArch64.Small.Chunk`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Small
open VG.Proof.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (stateAt serialize block)

def selected (n : Nat) : List Nat :=
  (List.finRange 4).flatMap (fun r => (lanes n).map (slot r))

theorem selected_mem (n : Nat) (hn : n ≤ 4) (k : Nat) (hk : k < 16) :
    k ∈ selected n ↔ k < 4*n :=
  (show ∀ n < 5, ∀ k < 16, k ∈ selected n ↔ k < 4*n by decide) n (by omega_using [hn]) k hk

theorem finish_ok {n : Nat} (hn : n ≤ 4) {s : State} {vs : Nat → CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s)
    (halias : s.gpr .x1 = s.gpr .x6 ∨ (⟨s.gpr .x1, 64*n⟩ : Region).Disjoint ⟨s.gpr .x6, 64*n⟩)
    (hin : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions (s.rd ++ s.wr)
      (s.gpr .x1 + BitVec.ofNat 64 (64*j+16*r)) 16)
    (hout : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s.wr
      (s.gpr .x6 + BitVec.ofNat 64 (64*j+16*r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap (VG.Impl.ChaCha20.AArch64.Neon4.finishRowForTo .x6 (lanes n)))) s fun s' =>
      (∀ k < 64*n, s'.mem (s.gpr .x6 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^ (serialize (vs (k/64))).getD (k%64) 0) ∧
      Frame [⟨s.gpr .x6, 64*n⟩] s.mem s'.mem ∧ Keep s s' := by
  have hj : (lanes n).Nodup := (List.nodup_finRange 4).sublist (List.filter_sublist)
  have hfit : ∀ r : Fin 4, ∀ j ∈ lanes n, 16 * slot r j + 16 ≤ 64 * n := by
    intro r j hj
    have hjn : j.val < n := by simpa [lanes] using hj
    unfold slot; omega_using [hjn]
  refine (finishRowsForTo_ok .x6 (lanes n) hj (List.finRange 4) (List.nodup_finRange 4)
    (DataTo.nil s.mem (s.gpr .x1) (s.gpr .x6) (64*n) (output vs)) rfl rfl halias (by omega_using [hn])
    (fun r _ i j => h (VG.Impl.ChaCha20.AArch64.Neon4.rowWord r i) j j.isLt)
    (fun _ _ _ _ => List.not_mem_nil) hfit hin hout).mono fun u ⟨hd,hs⟩ => ⟨?_,hd.frame,hs⟩
  intro k hk
  have hk256 : k < 256 := by omega_using [hn, hk]
  rw [hd _, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hk256] : k < 2^64),
    ite_eq_left ⟨List.mem_append_left _ ((selected_mem n hn (k/16) (by omega_using [hk256])).mpr (by omega_using [hk])),hk⟩,
    output_byte vs hk256]

theorem chunk_ok {sve : Bool} (n : Nat) (hn : n ≤ 4) (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (halias : s.gpr .x1 = s.gpr .x6 ∨ (⟨s.gpr .x1, 64*n⟩ : Region).Disjoint ⟨s.gpr .x6, 64*n⟩)
    (hsrc : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions (s.rd ++ s.wr)
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s.wr
      (s.gpr .x6 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (chunk n sve) s fun s' =>
      (∀ k < 64*n, s'.mem (s.gpr .x6 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x6, 64*n⟩] s.mem s'.mem ∧ ChunkKeep s s' := by
  apply WP.seq
  refine (setup_ok s hin).mono fun a ⟨ha, hsa, hta⟩ => ?_
  apply WP.seq
  refine (roundLoop_ok ha hta).mono fun b ⟨hb, hab⟩ => ?_
  have hsb : LoadSame s b := hsa.trans hab
  have hi : ∀ k : Fin 16, InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hsb.rd, hsb.wr, hsb.gpr _ (by decide)]; exact hin k
  apply WP.block_append
  refine (feed_ok hb hi).mono fun c ⟨hc, hbc⟩ => ?_
  have hsc := hsb.trans hbc
  have hc' : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => block (ctr (stateAt s.mem (s.gpr .x0)) j)) c := by
    intro k j hj
    simp only [block]
    rw [hc k j hj, input_same hsb, input_eq]
    simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  have h1 : c.gpr .x1 = s.gpr .x1 := hsc.gpr _ (by decide)
  have h6 : c.gpr .x6 = s.gpr .x6 := hsc.gpr _ (by decide)
  have hi' : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions (c.rd ++ c.wr) (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j hj; rw [hsc.rd, hsc.wr, h1]; exact hsrc r j hj
  have ho : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions c.wr (c.gpr .x6 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j hj; rw [hsc.wr, h6]; exact hout r j hj
  refine (finish_ok hn hc' (by rw [h1, h6]; exact halias) hi' ho).mono fun d ⟨hd, hf, hs⟩ => ⟨?_, ?_, ?_⟩
  · simpa only [h1, h6, hsc.mem] using hd
  · simpa only [h6, hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd, hs.wr.trans hsc.wr, hs.sp.trans hsc.sp⟩

end VG.Proof.ChaCha20.AArch64.Small

end

end

/-! ### `ChaCha20.AArch64.Small.Step`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Small
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp tp L bp stR dR tR bR S0 D0 KS Dst Src)
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)

/-- After `n` blocks of the vector kernel from `s₀` (where `x6` is the
destination): the destination done up to there and the source after it
intact, the pointers (the destination in `x4` and `x6`) advanced. -/
structure Prefix (s₀ : State) (n : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (64*n)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀-64*n)
  x3 : s.gpr .x3 = bp s₀
  x4 : s.gpr .x4 = tp s₀ + BitVec.ofNat 64 (64*n)
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) n
  data : Dst s₀ (64*n) s.mem
  src : Src s₀ (64*n) s.mem

theorem next_ok (s : State) (n : Nat) (hn : n ≤ 4)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block (next n)) s fun u =>
      u.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (64*n) ∧
      u.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 (64*n) ∧
      u.gpr .x4 = s.gpr .x6 + BitVec.ofNat 64 (64*n) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x6 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) n ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  have hi : n < 4096 := by omega_using [hn]
  have hb : 64*n < 4096 := by omega_using [hn]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, next,runBlock_cons,runBlock_nil,exec,
    VG.Impl.ChaCha20.AArch64.Xor.mov,
    addr,Size.bytes,Size.bits,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,hi,hb,Option.some.injEq,exists_eq_left',BitVec.add_zero]
  refine ⟨trivial,trivial,trivial,?_,?_,?_,trivial⟩
  · intro r h1 h2 h4 h6; simp only [h1,h2,h4,h6,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) n
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48+4 ≤ 64) (by decide))

theorem step_ok {sve : Bool} (s₀ : State) (hp : TPre s₀) (h6 : s₀.gpr .x6 = tp s₀) (n : Nat) (hn : n ≤ 4)
    (hle : 64*n ≤ L s₀) :
    WP isa (step n sve) s₀ (Prefix s₀ n) := by
  have hl : L s₀ < 2^64 := (s₀.gpr .x2).isLt
  have hi : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (st s₀+BitVec.ofNat 64 (4*k)) 4 := by
    intro k; rw [hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega_using []) (by omega_using [])⟩
  have hs : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions (s₀.rd ++ s₀.wr)
      (dp s₀+BitVec.ofNat 64 (64*j+16*r)) 16 := by
    intro r j hj
    have hjn : j.val < n := (List.mem_filter.mp hj).2 |> of_decide_eq_true
    rw [hp.rd,hp.wr]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega_using [hle, hjn]) (by omega_using [])⟩
  have ho : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s₀.wr
      (s₀.gpr .x6+BitVec.ofNat 64 (64*j+16*r)) 16 := by
    intro r j hj
    have hjn : j.val < n := (List.mem_filter.mp hj).2 |> of_decide_eq_true
    rw [hp.wr,h6]
    exact ⟨tR s₀,by simp,Offset.contains_base _ (by omega_using [hle, hjn]) (by omega_using [])⟩
  have sub : Region.Sub ⟨tp s₀,64*n⟩ (tR s₀) := Region.sub_prefix hle
  have ssub : Region.Sub ⟨dp s₀,64*n⟩ (dR s₀) := Region.sub_prefix hle
  have halias : s₀.gpr .x1 = s₀.gpr .x6 ∨
      (⟨s₀.gpr .x1, 64*n⟩ : Region).Disjoint ⟨s₀.gpr .x6, 64*n⟩ := by
    rw [h6]
    rcases hp.alias with he | hd
    · exact .inl he.symm
    · exact .inr ((hd.sub_left ssub).sub_right sub)
  apply WP.seq
  refine (chunk_ok (sve := sve) n hn s₀ hi halias hs ho).mono fun a ⟨ha,hf,hk⟩ => ?_
  rw [h6] at ha hf
  have ia : InRegions (a.rd ++ a.wr) (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.rd,hk.wr,hk.gpr .x0 (by decide),hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have oa : InRegions a.wr (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.wr,hk.gpr .x0 (by decide),hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hft : Frame [tR s₀] s₀.mem a.mem := hf.sub (fun r hr => by
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨tR s₀,by simp,sub⟩)
  have hd : Dst s₀ (64*n) a.mem := by
    intro k hkl
    by_cases hk' : k < 64*n
    · rw [ha k hk',ite_eq_left hk',keystream_getD _ hkl]
    · rw [hf _ (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        simp only [Region.Contains,tp,Mem.sub_ofNat_toNat _ (by omega_using [hl, hkl] : k < 2^64)]
        omega_using [hk']),ite_eq_right hk']
  have hsrc : Src s₀ (64*n) a.mem := Xor.src_step hp (Nat.zero_le _)
    (fun k _ _ => rfl) hft hd
  refine (next_ok a n hn ia oa).mono fun u ⟨h1,h2,h4,hg,hcnt,hf',hrd,hwr,hsp⟩ => ?_
  have h0 : u.gpr .x0 = st s₀ := (hg _ (by decide) (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  have hnd : ∀ r ∈ [stR s₀], (tR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.st_t.symm
  have hns : ∀ r ∈ [stR s₀], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hp.st_d.symm
  rw [hk.gpr _ (by decide)] at hcnt hf'
  refine ⟨h0,?_,?_,?_,?_,?_,hrd.trans hk.rd,hwr.trans hk.wr,hsp.trans hk.sp,?_,
    hd.frame hf' hnd,hsrc.frame hf' hns⟩
  · rw [h1,hk.gpr _ (by decide)]
  · rw [h2,hk.gpr _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [L,BitVec.toNat_sub,BitVec.toNat_ofNat] at *
    omega_using [hle]
  · exact (hg _ (by decide) (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  · rw [h4,hk.gpr _ (by decide),h6]
  · intro r hr
    have hne : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x6 := by revert hr; decide +revert
    exact (hg r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2).trans (hk.gpr r hne.2.2.1)
  · rw [hcnt, VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hp.st_t.sub_right sub)]

end VG.Proof.ChaCha20.AArch64.Small

end

end


@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp tp L bp stR dR tR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt serialize block)

/-- The scalar stream after `n` blocks of the vector kernel. -/
theorem tail_ok {s₀ : State} (hp : TPre s₀) {n : Nat} {s : State} (h : Prefix s₀ n s) (hle : 64*n ≤ L s₀) :
    WP isa Impl.ChaCha20.AArch64.Xor.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 :=
  (Xor.rest_ok BlockImpl.scalar.xorNoFrames (fun s hs _ => Xor.xor_gpr BlockImpl.scalar s hs) hp
    (n := 64*n) hle (by omega_using []) h.x0 h.x1 h.x2 h.x3 h.x4 h.rd h.wr
    (by rw [h.cnt, show 64*n/64 = n by omega_using []]) h.data h.src).mono fun _ ⟨ha, hpost, h0, h1⟩ =>
    ⟨⟨fun r hr => (ha.1 r hr).trans (h.cs r hr), ha.2.trans h.sp⟩, hpost, h0, h1⟩

structure CheckKeep (s a : State) : Prop where
  gpr : ∀ r, r ≠ .x5 → r ≠ .x6 → a.gpr r = s.gpr r
  mem : a.mem = s.mem
  rd : a.rd = s.rd
  wr : a.wr = s.wr
  sp : a.sp = s.sp

theorem CheckKeep.pre {s a : State} (h : CheckKeep s a) (hp : xorAArch64.pre s) :
    xorAArch64.pre a := by
  simpa only [xorAArch64,h.rd,h.wr,h.gpr .x0 (by decide) (by decide),h.gpr .x1 (by decide) (by decide),
    h.gpr .x2 (by decide) (by decide),h.gpr .x3 (by decide) (by decide),
    h.gpr .x4 (by decide) (by decide)] using hp

theorem CheckKeep.finish {s a u : State} (h : CheckKeep s a)
    (hu : GprAbi a u ∧ xorAArch64.post a u ∧ u.gpr .x0=a.gpr .x0 ∧ u.gpr .x1=a.gpr .x3) :
    GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  obtain ⟨hab,hp,h0,h1⟩ := hu
  refine ⟨⟨?_,hab.2.trans h.sp⟩,?_,h0.trans (h.gpr _ (by decide) (by decide)),
    h1.trans (h.gpr _ (by decide) (by decide))⟩
  · intro r hr
    have hn : r ≠ .x5 ∧ r ≠ .x6 := by revert hr; decide +revert
    exact (hab.1 r hr).trans (h.gpr r hn.1 hn.2)
  · simpa only [xorAArch64,h.mem,h.gpr .x0 (by decide) (by decide),h.gpr .x1 (by decide) (by decide),
      h.gpr .x2 (by decide) (by decide),h.gpr .x4 (by decide) (by decide)] using hp

theorem check_ok (s : State) (b : Nat) (hb : b < 64) :
    WP isa (.block [.lsr .x .x5 .x2 b]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (L s / 2^b) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,hb,Option.some.injEq,isa,runStep_some,exists_eq_left']
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · intro r hr _; exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.gpr_write_self,BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.setWidth_eq,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .x2).isLt)).symm

theorem check_zero {s : State} {n b : Nat} (_hb : b < 64) (hn : n < 2^64)
    (h : s.gpr .x5=BitVec.ofNat 64 (n/2^b)) :
    isa.eval (.zero .x .x5) s = some (decide (n < 2^b)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from Xor.eval_zero s .x5,h,Xor.ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
  congr 2
  simp only [Nat.div_eq_zero_iff,show 2^b ≠ 0 from Nat.ne_of_gt (Nat.two_pow_pos b),false_or]

theorem check3_ok (s : State) (hl : L s < 256) :
    WP isa (.block [.lsr .x .x5 .x2 6,.subImm .x .x5 .x5 3,.lsr .x .x5 .x5 63]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (if L s < 192 then 1 else 0) ∧
      a.gpr .x6 = s.gpr .x6 := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,Option.some.injEq,isa,runStep_some,exists_eq_left',
    RegUpd.gpr_write_self]
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · intro r hr _;simp only [RegUpd.gpr_write,hr,ite_false]
  · simp only [BitVec.setWidth_eq]
    have he : s.gpr .x2 >>> 6 = BitVec.ofNat 64 (L s/64) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by omega_arith)).symm
    rw [he]
    have hq : L s/64 < 4 := by omega_arith
    have hcases : L s/64=0 ∨ L s/64=1 ∨ L s/64=2 ∨ L s/64=3 := by omega_arith
    rcases hcases with h|h|h|h <;>
      simp only [show (L s < 192) ↔ (L s/64 < 3) by omega_arith,h] <;> decide
  · simp only [RegUpd.gpr_write,show Reg.x6 ≠ .x5 by decide,ite_false]

theorem check3_nonzero {s : State} {n : Nat}
    (h : s.gpr .x5=BitVec.ofNat 64 (if n < 192 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 192)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 192 <;> simp [hn]

/-- `short`'s first block: the check, and the destination copied to `x6`. -/
theorem check7_ok (s : State) :
    WP isa (.block [.lsr .x .x5 .x2 7, Impl.ChaCha20.AArch64.Xor.mov .x6 .x4]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (L s / 2^7) ∧ a.gpr .x6 = s.gpr .x4 := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons,runBlock_nil,exec,State.read,
    Impl.ChaCha20.AArch64.Xor.mov,Size.bits,Option.some.injEq,isa,runStep_some,exists_eq_left',
    BitVec.add_zero]
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · intro r h5 h6; simp only [RegUpd.gpr_write,h5,h6,ite_false]
  · simp only [RegUpd.gpr_write,show Reg.x5 ≠ .x6 by decide,ite_false,ite_true,BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .x2).isLt)).symm
  · simp only [RegUpd.gpr_write,ite_true,show Reg.x4 ≠ .x5 by decide,ite_false,BitVec.setWidth_eq]

theorem short_ok {sve : Bool} (s : State) (hp : xorAArch64.pre s) (hl : L s < 256) :
    WP isa (Impl.ChaCha20.AArch64.Small.short sve) s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.seq
  refine (check7_ok s).mono fun a ⟨ha,h5,h6⟩ => ?_
  apply WP.ite (decide (L s < 128)) (check_zero (by decide) (Xor.L_lt s) h5)
  · intro _
    exact (Xor.xor_gpr BlockImpl.scalar a (ha.pre hp)).mono fun _ h => ha.finish h
  · intro hshort
    have hge : 128 ≤ L s := by have := of_decide_eq_false hshort;omega_arith
    apply WP.seq
    apply WP.seq
    refine (check3_ok a (by simpa only [L,ha.gpr .x2 (by decide) (by decide)] using hl)).mono
      fun b ⟨hb,hb5,hb6⟩ => ?_
    have hla : L a=L s := by simp only [L,ha.gpr .x2 (by decide) (by decide)]
    rw [hla] at hb5
    have hpb := Xor.TPre.of b (hb.pre (ha.pre hp))
    have hb6' : b.gpr .x6 = tp b := by
      rw [hb6, h6, ← ha.gpr .x4 (by decide) (by decide), ← hb.gpr .x4 (by decide) (by decide)]
    apply WP.ite (decide (L s < 192)) (check3_nonzero hb5)
    · intro h192
      have hlen : 128 ≤ L b := by
        simp only [L,hb.gpr .x2 (by decide) (by decide),ha.gpr .x2 (by decide) (by decide)];exact hge
      exact ((step_ok (sve := sve) b hpb hb6' 2 (by decide) hlen).mono fun c hc =>
        (tail_ok hpb hc hlen).mono fun _ hu => ha.finish (hb.finish hu))
    · intro h192
      have hge192 : 192 ≤ L s := by have := of_decide_eq_false h192;omega_arith
      have hlen : 192 ≤ L b := by
        simp only [L,hb.gpr .x2 (by decide) (by decide),ha.gpr .x2 (by decide) (by decide)];exact hge192
      exact ((step_ok (sve := sve) b hpb hb6' 3 (by decide) hlen).mono fun c hc =>
        (tail_ok hpb hc hlen).mono fun _ hu => ha.finish (hb.finish hu))

theorem short_noFrames (sve : Bool) : (Impl.ChaCha20.AArch64.Small.short sve).noFrames = true := by
  cases sve <;> lit_decide

/-- `short` after the four-block chunks: run on the data the chunks left. -/
theorem tail_short {sve : Bool} {s₀ : State} (hp : TPre s₀) {t : Nat} {s : State} (h : Neon4.LInv s₀ t s)
    (hlt : L s₀ - 256 * t < 256) :
    WP isa (Impl.ChaCha20.AArch64.Small.short sve) s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 :=
  (Xor.rest_ok (short_noFrames sve) (fun s hs hl => short_ok (sve := sve) s hs (by rw [hl]; exact hlt))
    hp (n := 256 * t) h.le (by omega_using []) h.x0 h.x1 h.x2 h.x3 h.x4 h.rd h.wr
    (by rw [h.cnt, show 256 * t / 64 = 4 * t by omega_using []]) h.data h.src).mono fun _ ⟨ha, hpost, h0, h1⟩ =>
    ⟨⟨fun r hr => (ha.1 r hr).trans (h.keep r (by intro he; subst he; simp [preserved] at hr)
      (by intro he; subst he; simp [preserved] at hr) (by intro he; subst he; simp [preserved] at hr)
      (by intro he; subst he; simp [preserved] at hr) (by intro he; subst he; simp [preserved] at hr)),
      ha.2.trans h.sp⟩, hpost, h0, h1⟩

theorem correct {sve : Bool} (s : State) (hp : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Small.xor sve) s fun u =>
      abiPreserved s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.withPreservedV (hc := by cases sve <;> lit_decide)
  apply WP.seq
  refine (Neon4.init_ok s).mono fun u ⟨hi, h5⟩ => ?_
  apply WP.seq
  refine (Neon4.bulk_ok (Xor.TPre.of s hp) hi h5).mono fun v ⟨t, hlt, hv⟩ => ?_
  exact tail_short (sve := sve) (Xor.TPre.of s hp) hv hlt

theorem xor_noFrames (sve : Bool) : (Impl.ChaCha20.AArch64.Small.xor sve).noFrames = true := by
  cases sve <;> lit_decide

end VG.Proof.ChaCha20.AArch64.Small

end

end

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega_using [hks, hk])] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega_using [hks, hk]),
    Option.getD_some]
  simpa using e

/-- The rest after the chunks, with `Small.xor`. -/
theorem ttail_ok {sve : Bool} {s₀ : State} (hp : VG.Proof.ChaCha20.AArch64.Xor.TPre s₀) {t : Nat}
    {s : State} (h : TRest s₀ t s) :
    WP isa (Impl.ChaCha20.AArch64.Small.xor sve) s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 :=
  (VG.Proof.ChaCha20.AArch64.Xor.rest_ok (VG.Proof.ChaCha20.AArch64.Small.xor_noFrames sve)
    (fun s hs _ => (VG.Proof.ChaCha20.AArch64.Small.correct s hs).mono fun _ ⟨ha, hu⟩ =>
      ⟨⟨ha.1, ha.2.1⟩, hu⟩)
    hp (n := 512 * t) h.le (by omega_using []) h.x0 h.x1 h.x2 h.x3 h.x4 h.rd h.wr
    (by rw [h.cnt, show 512 * t / 64 = 8 * t by omega_using []]) h.data h.src).mono
    fun _ ⟨ha, hpost, h0, h1⟩ => ⟨⟨fun r hr => (ha.1 r hr).trans (h.cs r hr), ha.2.trans h.sp⟩, hpost, h0, h1⟩

end VG.Proof.ChaCha20.AArch64.Mixed8
