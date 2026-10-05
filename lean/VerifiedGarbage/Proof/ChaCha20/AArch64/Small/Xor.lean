import VerifiedGarbage.Impl.ChaCha20.AArch64.Small
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Chunk`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Small
open VG.Proof.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (stateAt serialize block)

def selected (n : Nat) : List Nat :=
  (List.finRange 4).flatMap (fun r => (lanes n).map (slot r))

theorem selected_mem (n : Nat) (hn : n ≤ 4) (k : Nat) (hk : k < 16) :
    k ∈ VG.Proof.ChaCha20.AArch64.Small.selected n ↔ k < 4*n :=
  (show ∀ n < 5, ∀ k < 16, k ∈ VG.Proof.ChaCha20.AArch64.Small.selected n ↔ k < 4*n by decide) n (by omega) k hk

theorem finish_ok {n : Nat} (hn : n ≤ 4) {s : State} {vs : Nat → CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s)
    (hout : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64*j+16*r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap (VG.Impl.ChaCha20.AArch64.Neon4.finishRowFor (lanes n)))) s fun s' =>
      (∀ k < 64*n, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^ (serialize (vs (k/64))).getD (k%64) 0) ∧
      Frame [⟨s.gpr .x1, 64*n⟩] s.mem s'.mem ∧ Keep s s' := by
  have hj : (lanes n).Nodup := (List.nodup_finRange 4).sublist (List.filter_sublist)
  refine (finishRowsFor_ok (lanes n) hj (List.finRange 4) (List.nodup_finRange 4)
    (Data.nil s.mem (s.gpr .x1) (output vs)) rfl (fun r _ i j => h (VG.Impl.ChaCha20.AArch64.Neon4.rowWord r i) j j.isLt)
    (fun _ _ _ _ => List.not_mem_nil) hout).mono fun u ⟨hd,hs⟩ => ⟨?_,?_,hs⟩
  · intro k hk
    have hk256 : k < 256 := by omega
    rw [hd _, Mem.sub_ofNat_toNat _ (by omega : k < 2^64),
      ite_eq_left ⟨List.mem_append_left _ ((VG.Proof.ChaCha20.AArch64.Small.selected_mem n hn (k/16) (by omega)).mpr (by omega)),hk256⟩,
      output_byte vs hk256]
  · intro x hx
    have hnot : ¬ (x-s.gpr .x1).toNat < 64*n := by
      have h := hx ⟨s.gpr .x1,64*n⟩ (List.mem_cons_self ..)
      simp only [Region.Contains] at h
      omega
    rw [hd x, ite_eq_right]
    intro hh
    have hmem : (x-s.gpr .x1).toNat/16 ∈ VG.Proof.ChaCha20.AArch64.Small.selected n := by simpa only [VG.Proof.ChaCha20.AArch64.Small.selected, List.append_nil] using hh.1
    have := (VG.Proof.ChaCha20.AArch64.Small.selected_mem n hn ((x-s.gpr .x1).toNat/16) (by omega)).mp hmem
    omega

theorem chunk_ok (n : Nat) (hn : n ≤ 4) (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (VG.Impl.ChaCha20.AArch64.Small.chunk n) s fun s' =>
      (∀ k < 64*n, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1, 64*n⟩] s.mem s'.mem ∧ ChunkKeep s s' := by
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
  have hc' : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) j)) c := by
    intro k j hj
    simp only [VG.Spec.ChaCha20.block]
    rw [hc k j hj, input_same hsb, input_eq]
    simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  have ho : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j hj; rw [hsc.wr, hsc.gpr _ (by decide)]; exact hout r j hj
  refine (VG.Proof.ChaCha20.AArch64.Small.finish_ok hn hc' ho).mono fun d ⟨hd, hf, hs⟩ => ⟨?_, ?_, ?_⟩
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hd
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd, hs.wr.trans hsc.wr, hs.sp.trans hsc.sp⟩

end VG.Proof.ChaCha20.AArch64.Small

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit`. -/
section

namespace VG
materialize_code Impl.ChaCha20.AArch64.Small.xor
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Step`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Small
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)

structure Prefix (s₀ : State) (n : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (64*n)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀-64*n)
  x3 : s.gpr .x3 = bp s₀
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) n
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    s₀.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (if k < 64*n then (KS s₀).getD k 0 else 0)
  frame : Frame [stR s₀,dR s₀,bR s₀] s₀.mem s.mem

theorem next_ok (s : State) (n : Nat) (hn : n ≤ 4)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block (VG.Impl.ChaCha20.AArch64.Small.next n)) s fun u =>
      u.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (64*n) ∧
      u.gpr .x2 = s.gpr .x2 - BitVec.ofNat 64 (64*n) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) n ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  have hi : n < 4096 := by omega
  have hb : 64*n < 4096 := by omega
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, VG.Impl.ChaCha20.AArch64.Small.next,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,hi,hb,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,trivial,?_,?_,?_,trivial⟩
  · intro r h1 h2 h4; simp only [h1,h2,h4,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) n
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48+4 ≤ 64) (by decide))

theorem step_ok (s₀ : State) (hp : XPre s₀) (n : Nat) (hn : n ≤ 4) (hle : 64*n ≤ L s₀) :
    WP isa (step n) s₀ (VG.Proof.ChaCha20.AArch64.Small.Prefix s₀ n) := by
  have hl : L s₀ < 2^64 := (s₀.gpr .x2).isLt
  have hi : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (st s₀+BitVec.ofNat 64 (4*k)) 4 := by
    intro k; rw [hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  have ho : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s₀.wr
      (dp s₀+BitVec.ofNat 64 (64*j+16*r)) 16 := by
    intro r j hj
    have hjn : j.val < n := (List.mem_filter.mp hj).2 |> of_decide_eq_true
    rw [hp.wr]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Small.chunk_ok n hn s₀ hi ho).mono fun a ⟨ha,hf,hk⟩ => ?_
  have ia : InRegions (a.rd ++ a.wr) (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.rd,hk.wr,hk.gpr .x0 (by decide),hp.rd,hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have oa : InRegions a.wr (a.gpr .x0+BitVec.ofNat 64 48) 4 := by
    rw [hk.wr,hk.gpr .x0 (by decide),hp.wr]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have sub : Region.Sub ⟨dp s₀,64*n⟩ (dR s₀) := Region.sub_prefix hle
  refine (VG.Proof.ChaCha20.AArch64.Small.next_ok a n hn ia oa).mono fun u ⟨h1,h2,hg,hcnt,hf',hrd,hwr,hsp⟩ => ?_
  have h0 : u.gpr .x0 = st s₀ := (hg _ (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  refine ⟨h0,?_,?_,?_,?_,hrd.trans hk.rd,hwr.trans hk.wr,hsp.trans hk.sp,?_,?_,?_⟩
  · rw [h1,hk.gpr _ (by decide)]
  · rw [h2,hk.gpr _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [L,BitVec.toNat_sub,BitVec.toNat_ofNat] at *
    omega
  · exact (hg _ (by decide) (by decide) (by decide)).trans (hk.gpr _ (by decide))
  · intro r hr
    have hne : r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 := by revert hr; decide +revert
    exact (hg r hne.1 hne.2.1 hne.2.2).trans (hk.gpr r hne.2.2)
  ·
    rw [hk.gpr _ (by decide)] at hcnt
    rw [hcnt, VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact hp.st_d.sub_right sub)]
  ·
    intro k hkl
    have inData : (dR s₀).Contains (dp s₀+BitVec.ofNat 64 k) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    have nd : ¬ (stR s₀).Contains (dp s₀+BitVec.ofNat 64 k) 1 := fun h => hp.st_d _ h inData
    have eu : u.mem (dp s₀+BitVec.ofNat 64 k) = a.mem (dp s₀+BitVec.ofNat 64 k) := by
      apply hf'; intro r hr
      simp only [List.mem_singleton] at hr; subst r
      rw [hk.gpr _ (by decide)]
      exact nd
    rw [eu]
    by_cases hk' : k < 64*n
    · rw [ha k hk',ite_eq_left hk',keystream_getD _ hkl]
    · rw [hf _ (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        simp only [Region.Contains,dp,Mem.sub_ofNat_toNat _ (by omega : k < 2^64)]
        omega),ite_eq_right hk']
      simp
  · exact (hf.sub (fun r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨dR s₀,by simp,sub⟩)).trans (hf'.sub (fun r hr => by
        simp only [List.mem_singleton] at hr; subst r
        rw [hk.gpr _ (by decide)]
        exact ⟨stR s₀,by simp,fun _ h => h⟩))

end VG.Proof.ChaCha20.AArch64.Small

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt serialize block)
open VG.Proof.ChaCha20.AArch64.Neon4 (data_in)

theorem ks_shift (S : CState) {len n k : Nat} (hk : k < len) (ht : 64*n ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (VG.Spec.ChaCha20.block (ctr (ctr S n) ((k-64*n)/64)))).getD ((k-64*n)%64) 0 := by
  rw [keystream_getD _ hk,Neon4.ctr_add,
    show n+(k-64*n)/64=k/64 by omega,show (k-64*n)%64=k%64 by omega]

abbrev tailR (s₀ : State) (n : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (64 * n), L s₀ - 64 * n⟩

theorem tail_sub {s₀ : State} {n : Nat} (ht : 64 * n ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Small.tailR s₀ n) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {n k : Nat} (hk : k < 64 * n) (ht : 64 * n ≤ L s₀) :
    ¬ (VG.Proof.ChaCha20.AArch64.Small.tailR s₀ n).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := Xor.L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

theorem tail_ok {s₀ : State} (hp : XPre s₀) {n : Nat} {s : State} (h : VG.Proof.ChaCha20.AArch64.Small.Prefix s₀ n s) (hle : 64*n ≤ L s₀) :
    WP isa Impl.ChaCha20.AArch64.Xor.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hn : (BitVec.ofNat 64 (L s₀ - 64 * n)).toNat = L s₀ - 64 * n :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let wr := [stR s₀, VG.Proof.ChaCha20.AArch64.Small.tailR s₀ n, bR s₀]
  have hs : xorAArch64.pre (s.withRegions [] wr) := by
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      h.x0, h.x1, h.x2, h.x3, hn]
    have ts := VG.Proof.ChaCha20.AArch64.Small.tail_sub hle
    exact ⟨trivial, rfl, hp.st_d.sub_right ts, hp.st_b, hp.d_b.sub_left ts, by
      have := hp.nowrap
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega⟩
  have hc : Covers wr s.wr := by
    rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s₀, by simp, 64 * n, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hw : WP isa Impl.ChaCha20.AArch64.Xor.xor (s.withRegions [] wr) fun u =>
      abiPreserved (s.withRegions [] wr) u ∧ xorAArch64.post (s.withRegions [] wr) u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 :=
    Xor.xor_x1 BlockImpl.scalar _ hs
  refine WP.narrow hw ?_ hc ?_ BlockImpl.scalar.xorNoFrames
  · rw [h.rd, hp.rd]; exact hc
  · intro u _ _ hsp hf ⟨ha, hpost, h0, h1⟩
    simp only [State.withRegions_gpr, State.withRegions_sp, abiPreserved] at ha
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      h.x0, h.x1, h.x2, hn, h.cnt] at hpost
    refine ⟨⟨?_, hsp.trans h.sp⟩, ?_, h0.trans h.x0, h1.trans h.x3⟩
    · intro r hr
      rw [ha.1 r hr]
      exact h.cs r hr
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < L s₀ := hk
      have ns : ¬ (stR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.st_d _ hh (data_in hk)
      have nb : ¬ (bR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.d_b _ (data_in hk) hh
      by_cases hk' : k < 64 * n
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact VG.Proof.ChaCha20.AArch64.Small.not_tail hk' hle
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (64 * n) + BitVec.ofNat 64 (k - 64 * n) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := VG.Proof.ChaCha20.AArch64.Small.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 64 * n) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, VG.Proof.ChaCha20.AArch64.Small.ks_shift _ hk (n := n) (by omega)]
        simp


structure CheckKeep (s a : State) : Prop where
  gpr : ∀ r, r ≠ .x5 → a.gpr r = s.gpr r
  mem : a.mem = s.mem
  rd : a.rd = s.rd
  wr : a.wr = s.wr
  sp : a.sp = s.sp

theorem CheckKeep.pre {s a : State} (h : VG.Proof.ChaCha20.AArch64.Small.CheckKeep s a) (hp : xorAArch64.pre s) :
    xorAArch64.pre a := by
  simpa only [xorAArch64,h.rd,h.wr,h.gpr .x0 (by decide),h.gpr .x1 (by decide),
    h.gpr .x2 (by decide),h.gpr .x3 (by decide)] using hp

theorem CheckKeep.finish {s a u : State} (h : VG.Proof.ChaCha20.AArch64.Small.CheckKeep s a)
    (hu : GprAbi a u ∧ xorAArch64.post a u ∧ u.gpr .x0=a.gpr .x0 ∧ u.gpr .x1=a.gpr .x3) :
    GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  obtain ⟨hab,hp,h0,h1⟩ := hu
  refine ⟨⟨?_,hab.2.trans h.sp⟩,?_,h0.trans (h.gpr _ (by decide)),h1.trans (h.gpr _ (by decide))⟩
  · intro r hr
    have hn : r ≠ .x5 := by revert hr; decide +revert
    exact (hab.1 r hr).trans (h.gpr r hn)
  · simpa only [xorAArch64,h.mem,h.gpr .x0 (by decide),h.gpr .x1 (by decide),
      h.gpr .x2 (by decide)] using hp

theorem check_ok (s : State) (b : Nat) (hb : b < 64) :
    WP isa (.block [.lsr .x .x5 .x2 b]) s fun a =>
      VG.Proof.ChaCha20.AArch64.Small.CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (L s / 2^b) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,hb,Option.some.injEq,isa,runStep_some,exists_eq_left']
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · intro r hr; exact RegUpd.gpr_write_of_ne _ _ _ hr
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
      VG.Proof.ChaCha20.AArch64.Small.CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (if L s < 192 then 1 else 0) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,Option.some.injEq,isa,runStep_some,exists_eq_left',
    RegUpd.gpr_write_self]
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · intro r hr;simp only [RegUpd.gpr_write,hr,ite_false]
  · simp only [BitVec.setWidth_eq]
    have he : s.gpr .x2 >>> 6 = BitVec.ofNat 64 (L s/64) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [he]
    have hq : L s/64 < 4 := by omega
    have hcases : L s/64=0 ∨ L s/64=1 ∨ L s/64=2 ∨ L s/64=3 := by omega
    rcases hcases with h|h|h|h <;>
      simp only [show (L s < 192) ↔ (L s/64 < 3) by omega,h] <;> decide

theorem check3_nonzero {s : State} {n : Nat}
    (h : s.gpr .x5=BitVec.ofNat 64 (if n < 192 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 192)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 192 <;> simp [hn]

theorem stepped (s : State) (hp : xorAArch64.pre s) (n : Nat) (hn : n ≤ 4) (hl : 64*n ≤ L s) :
    WP isa (.seq (Impl.ChaCha20.AArch64.Small.step n) Impl.ChaCha20.AArch64.Xor.xor) s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.seq
  exact (VG.Proof.ChaCha20.AArch64.Small.step_ok s (XPre.of s hp) n hn hl).mono fun _ h => VG.Proof.ChaCha20.AArch64.Small.tail_ok (XPre.of s hp) h hl

theorem short_ok (s : State) (hp : xorAArch64.pre s) (hl : L s < 256) :
    WP isa Impl.ChaCha20.AArch64.Small.short s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Small.check_ok s 7 (by decide)).mono fun a ⟨ha,h5⟩ => ?_
  apply WP.ite (decide (L s < 128)) (VG.Proof.ChaCha20.AArch64.Small.check_zero (by decide) (Xor.L_lt s) h5)
  · intro _
    have hw : WP isa Impl.ChaCha20.AArch64.Xor.xor a fun u =>
      abiPreserved a u ∧ xorAArch64.post a u ∧ u.gpr .x0=a.gpr .x0 ∧ u.gpr .x1=a.gpr .x3 :=
        Xor.xor_x1 BlockImpl.scalar a (ha.pre hp)
    exact hw.mono fun _ h => ha.finish ⟨⟨h.1.1,h.1.2.1⟩,h.2⟩
  · intro hshort
    have hge : 128 ≤ L s := by have := of_decide_eq_false hshort;omega
    apply WP.seq
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Small.check3_ok a (by simpa only [L,ha.gpr .x2 (by decide)] using hl)).mono fun b ⟨hb,hb5⟩ => ?_
    have hla : L a=L s := by simp only [L,ha.gpr .x2 (by decide)]
    rw [hla] at hb5
    apply WP.ite (decide (L s < 192)) (VG.Proof.ChaCha20.AArch64.Small.check3_nonzero hb5)
    · intro h192
      have hlen : 128 ≤ L b := by simp only [L,hb.gpr .x2 (by decide),ha.gpr .x2 (by decide)];exact hge
      exact ((VG.Proof.ChaCha20.AArch64.Small.step_ok b (XPre.of b (hb.pre (ha.pre hp))) 2 (by decide) hlen).mono fun c hc =>
        (VG.Proof.ChaCha20.AArch64.Small.tail_ok (XPre.of b (hb.pre (ha.pre hp))) hc hlen).mono fun _ hu => ha.finish (hb.finish hu))
    · intro h192
      have hge192 : 192 ≤ L s := by have := of_decide_eq_false h192;omega
      have hlen : 192 ≤ L b := by simp only [L,hb.gpr .x2 (by decide),ha.gpr .x2 (by decide)];exact hge192
      exact ((VG.Proof.ChaCha20.AArch64.Small.step_ok b (XPre.of b (hb.pre (ha.pre hp))) 3 (by decide) hlen).mono fun c hc =>
        (VG.Proof.ChaCha20.AArch64.Small.tail_ok (XPre.of b (hb.pre (ha.pre hp))) hc hlen).mono fun _ hu => ha.finish (hb.finish hu))

theorem correct (s : State) (hp : xorAArch64.pre s) :
    WP isa Impl.ChaCha20.AArch64.Small.xor s fun u =>
      abiPreserved s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.withPreservedV (hc := by lit_decide)
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Small.check_ok s 8 (by decide)).mono fun a ⟨ha,h5⟩ => ?_
  apply WP.ite (decide (L s < 256)) (VG.Proof.ChaCha20.AArch64.Small.check_zero (by decide) (Xor.L_lt s) h5)
  · intro hshort
    have hlen : L a < 256 := by simp only [L,ha.gpr .x2 (by decide)];exact of_decide_eq_true hshort
    exact (VG.Proof.ChaCha20.AArch64.Small.short_ok a (ha.pre hp) hlen).mono fun _ hu => ha.finish hu
  · intro _
    exact (Neon4.correct a (ha.pre hp)).mono fun _ h => ha.finish ⟨⟨h.1.1,h.1.2.1⟩,h.2⟩

theorem xor_noFrames : Impl.ChaCha20.AArch64.Small.xor.noFrames=true := by lit_decide

end VG.Proof.ChaCha20.AArch64.Small

end
