module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Loop
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # RSA key generation's controller on PPC64LE: correctness

The entry, the frame saving the link register with the key's buffer cleared
but `p` and the loop in it, and the return: the contract's postcondition and
what the calling convention preserves.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch
open VG.Proof.Rsa.PPC64LE (InvLaw)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.RsaKeyGen.PPC64LE.Search (WP.keepS)

/-- The controller, with the prime search and the key it calls. -/
abbrev genCode (v : RoundImpl) : Prog isa := code (searchCall v) keyCall

/-- The return: the octets consumed to `used`, the status, and `r31`. -/
theorem finish_ok {p : GenPublic} {original d y : State} {final : KeySearchResult}
    (g : GenDone p original final d) (hm : y.mem = d.mem) (hw : y.wr = d.wr) (h31 : y.gpr .r31 = p.F) :
    WP isa (.block finish) y fun t =>
      ((t.gpr .r3 = BitVec.ofNat 64 final.keyStatus ∧ t.gpr .r31 = original.gpr .r31 ∧
        t.mem = y.mem.writeW (p.up + BitVec.ofNat 64 0) (BitVec.ofNat 64 final.used)) ∧
        Keep [.r3, .r5, .r6, .r31] y t) ∧ t.syms = y.syms := by
  obtain ⟨g, hst, -, -⟩ := g
  have hyw : y.wr = p.frame :: original.wr := hw.trans g.wr
  have scr := g.input.frame_scr hyw
  have hl : ∀ d, d + 8 ≤ 112 → InRegions (y.rd ++ y.wr) (p.F + BitVec.ofNat 64 d) 8 :=
    fun d hd => let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hus : Scr y p.up 8 := by
    have hn := g.input.nowrap (r := inUsed original) (by simp [inWrites])
    rw [g.used_region] at hn
    refine Scr.of_mem ?_ hn
    rw [hyw, g.input.wr_eq, ← g.used_region]
    simp [inWrites]
  have hsu : InRegions y.wr (p.up + BitVec.ofNat 64 0) 8 := hus.st (d := 0) (n := 8) (by decide)
  have h2 := g.slot (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := g.slot (j := 8) (v := BitVec.ofNat 64 final.used) (by simp [GenPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at h2 h8
  rw [← hm] at h2 h8
  have hnF : p.F.toNat + 112 ≤ 2 ^ 64 := scr.nowrap
  have hkeep (v : BitVec 64) (d : Nat) (hd : d + 8 ≤ 112) :
      (y.mem.writeW (p.up + BitVec.ofNat 64 0) v).readW (p.F + BitVec.ofNat 64 d) 64 =
        y.mem.readW (p.F + BitVec.ofNat 64 d) 64 :=
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (rU p)) v
      (by rw [BitVec.add_zero]; exact Region.contains_self _ _)).readW
      (r := p.frame) (Offset.contains_base _ hd (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact g.input.frame_disjoint_writes (r := inUsed original) (by simp [inWrites]) |>.sub_right
          (by rw [g.used_region]; exact fun _ h => h)) (by decide)
  have h9 : y.mem.readW (p.F + BitVec.ofNat 64 72) 64 = original.gpr .r31 := by rw [hm]; exact g.savedR31
  have h10 : y.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 final.keyStatus := by rw [hm]; exact hst
  have hk9 : ∀ v : BitVec 64, (y.mem.writeW (p.up + BitVec.ofNat 64 0) v).readW (p.F + BitVec.ofNat 64 72) 64 =
      original.gpr .r31 := fun v => (hkeep v 72 (by decide)).trans h9
  have hk10 : ∀ v : BitVec 64, (y.mem.writeW (p.up + BitVec.ofNat 64 0) v).readW (p.F + BitVec.ofNat 64 80) 64 =
      BitVec.ofNat 64 final.keyStatus := fun v => (hkeep v 80 (by decide)).trans h10
  refine WP.keepS [.r3, .r5, .r6, .r31] ?_ (by decide)
  unfold finish
  prun [ldf, h31, hl 16 (by decide), hl 64 (by decide), hl 72 (by decide), hl 80 (by decide), hsu, h2, h8,
    hk9, hk10]

theorem phase_word_if (ph : KeyPhase) :
    BitVec.ofNat 64 (phaseWord ph) = BitVec.ofNat 64 (if ph = .p then 0 else 1) := by
  cases ph <;> rfl

/-- What the controller returns, from what the loop leaves. -/
theorem done_post {p : GenPublic} {s d t : State} (hp : GenInput p s)
    (h : GenDone p s (genResult s) d)
    (hax : t.gpr .r3 = BitVec.ofNat 64 (genResult s).keyStatus)
    (hm : t.mem = d.mem.writeW (p.up + BitVec.ofNat 64 0) (BitVec.ofNat 64 (genResult s).used)) :
    genPost s t := by
  obtain ⟨g, -, hkey, req, hreq, hr⟩ := h
  have hf := hp.cfacts
  have hst := g.state
  have hkp : s.gpr .r3 = p.kp := by rw [← hp.2]; rfl
  have hup : s.gpr .r5 = p.up := by rw [← hp.2]; rfl
  have hstp : s.gpr .r10 = p.stp := by rw [← hp.2]; rfl
  have hL : genLen s = p.L := by rw [← hp.2]; rfl
  have heB : genE s = p.eB := by rw [← hp.2]; rfl
  have hfr : Frame [rU p] d.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (by rw [BitVec.add_zero]; exact Region.contains_self _ _)
  have hword (j : Nat) (hj : j < 7) : word t.mem p.stp (8 * j) = word d.mem p.stp (8 * j) :=
    hfr.readW (r := cS p) (Offset.contains_base _ (by omega) (by have := hf.nT; omega))
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hf.uT.symm) (by decide)
  have hbytes {R : Region} (hR : Region.Sub R (cK p) ∨ Region.Sub R (cS p)) (hn : R.len ≤ 2 ^ 64) :
      Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt d.mem R.base R.len := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    refine hfr.bytes (fun q hq => ?_) hn (List.mem_range.mp hi)
    obtain rfl := List.mem_singleton.mp hq
    rcases hR with hR | hR
    exacts [(hf.kU.sub_left hR), (hf.uT.symm.sub_left hR)]
  refine ⟨?_, ?_, ?_, req, ?_, ?_, ?_⟩
  · have := keyStatus_lt (genResult s)
    rw [hax, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [hkp, hL, ← hkey]
    exact hbytes (R := ⟨p.kp, 9 * p.L⟩) (.inl fun _ h => h) (by show 9 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
  · rw [hup]
    show [t.mem.readW (p.up + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [Nat.mul_zero, hm, Mem.readW_writeW_self64]
  · rw [hstp, hL]
    show [word t.mem p.stp (8 * 0), word t.mem p.stp (8 * 1), word t.mem p.stp (8 * 2), word t.mem p.stp (8 * 3),
      word t.mem p.stp (8 * 4), word t.mem p.stp (8 * 5)] = _
    rw [hword 0 (by decide), hword 1 (by decide), hword 2 (by decide), hword 3 (by decide), hword 4 (by decide),
      hword 5 (by decide)]
    simp only [Nat.reduceMul]
    rw [show word d.mem p.stp 0 = _ from hst.remaining, show word d.mem p.stp 8 = _ from hst.len,
      show word d.mem p.stp 16 = _ from hst.cap, show word d.mem p.stp 24 = _ from hreq,
      show word d.mem p.stp 32 = _ from hst.phase, show word d.mem p.stp 40 = _ from hst.left, phase_word_if]
  · rw [hstp, heB]
    have := hbytes (R := ⟨p.stp + BitVec.ofNat 64 48, 8⟩) (.inr rE_sub) (by show 8 ≤ 2 ^ 64; decide)
    exact this.trans hst.e
  · rw [hL]; exact hr

theorem iteration_sdepth (v : RoundImpl) : sdepth (iteration (searchCall v) keyCall) ≤ 896 := by
  have := search_sdepth v
  have hk := keyCode_sdepth
  simp only [iteration, seqs, searchRun, searchCall, classify, accepted, keyRun, keyCall, exhaustedGen, fail,
    afterKey, clearAll, clear, Impl.Bignum.PPC64LE.countLoop, sdepth, Instr.frameBytes, Search.searchCode, hk]
  omega

theorem clearAround_sdepth : sdepth clearAround = 0 := by
  simp only [clearAround, seqs, clear, Impl.Bignum.PPC64LE.countLoop, sdepth]
  rfl

/-- The key's buffer cleared but `p`, and the loop. -/
theorem gen_body_ok [InvLaw] (v : RoundImpl) {s t' : State} (hp : GenInput (genOfState s) s)
    (hl : GenFrame (genOfState s) s 0 (genProgress s) (framed .r0 t'))
    (hfb : Frame [below s.sp stackUse] s.mem (framed .r0 t').mem) :
    WP isa (.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .d .r9))) (framed .r0 t')
      (GenDone (genOfState s) s (genResult s)) := by
  have hf := hp.cfacts
  refine WP.seq (WP.mono (clearAround_ok hl ?_) fun w ⟨hw, _⟩ => ?_)
  · intro pB hpB
    simp only [genProgress, keyProgressAt] at hpB
    split at hpB
    · cases hpB
    · cases hpB
      obtain ⟨hL1, -, -⟩ := hf.len
      refine bytes_kept hfb ?_ (by show (genOfState s).L ≤ 2 ^ 64; have := hf.nK; omega)
      have hd := hp.stack_disjoint (r := inKey s) (by simp [inWrites])
      rw [hl.key_region] at hd
      exact hd.sub_right (slot_sub _ (by omega))
  have hinv : GenInv (genOfState s) s (genResult s) (genMeasure (genOfState s) 0 (genProgress s)) w :=
    ⟨0, genProgress s, rfl, hw, [], by rw [consume_zero]; rfl⟩
  exact gen_loop v hinv

/-- The frame saving the link register, around the body. -/
theorem gen_frame_ok [InvLaw] (v : RoundImpl) {s t' : State} (hp : GenInput (genOfState s) s)
    (kk : Keep entryRegs (allocated 144 s) t')
    (hl : GenFrame (genOfState s) s 0 (genProgress s) (framed .r0 t'))
    (hfb : Frame [below s.sp stackUse] s.mem (framed .r0 t').mem) :
    WP isa (.frame (.push .r0) (.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .d .r9)))
      (.pop .r0)) t' fun y => ∃ d, GenDone (genOfState s) s (genResult s) d ∧
        y = { d.write .r0 (t'.gpr .r0) with sp := t'.sp } := by
  have hroom := hp.room
  have hsp0 : (genOfState s).sp = s.sp := hp.sp_eq
  have hsu : stackUse = 1088 := rfl
  have hroom' : stackUse ≤ s.sp.toNat := by rw [← hsp0]; exact hroom
  have htsp : t'.sp = s.sp - BitVec.ofNat 64 144 := kk.sp
  have hsp48 : 48 ≤ t'.sp.toNat := by
    rw [htsp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_ofNat]; omega
  refine WP.frameRegAny hsp48 ?_ ?_ (by
    have := iteration_sdepth v
    simp only [sdepth, clearAround_sdepth]
    omega)
  · intro R hR
    rw [kk.wr, alloc_wr hp] at hR
    rw [htsp, sp_160]
    rcases List.mem_cons.mp hR with rfl | hR
    · rw [← hsp0]
      have hs := Offset.sep_below (genOfState s).sp 1088 (a := 160) (n := 16) (b := 112) (k := 112) (by decide)
        (by decide) (Or.inl (by decide)) (by decide) (by decide)
      exact fun x hx hy => hs x (Nat.lt_of_succ_le (by simpa only [Region.Contains] using hx))
        (Nat.lt_of_succ_le (by simpa only [Region.Contains, GenPublic.F] using hy))
    · rw [hp.wr_eq] at hR
      have hd := hp.stack_disjoint (r := R) (List.mem_append_left _ hR)
      exact hd.sub_left (Offset.sub_below s.sp (a := 160) (b := stackUse) (by decide) (by decide))
  exact WP.mono (gen_body_ok v hp hl hfb) fun d hd => ⟨d, hd, rfl⟩

theorem gen_correct_ok [InvLaw] (v : RoundImpl) {s : State} (h : genPre s) :
    WP isa (genCode v) s fun t => genPost s t ∧ abiPreserved s t := by
  have hp : GenInput (genOfState s) s := ⟨h, rfl⟩
  have hroom := hp.room
  have hf := hp.cfacts
  have hsp0 : (genOfState s).sp = s.sp := hp.sp_eq
  have hsu : stackUse = 1088 := rfl
  have hroom' : stackUse ≤ s.sp.toNat := by rw [← hsp0]; exact hroom
  unfold genCode code
  refine WP.alloc (by decide) (alloc_room hroom') ?_
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (VG.PPC64LE.WP.mono_syms (entryHead_ok hp) fun u ⟨⟨hx, hmu⟩, ku⟩ hyu =>
    VG.PPC64LE.WP.mono_syms (entryWords_ok hp hx hmu ku) fun t ⟨hmt, kt⟩ hyt => ?_))
  have hm0 : t.mem = writeFrame (allocated 144 s).mem (genOfState s).F (entryValues s) := by
    rw [hmt, hmu, entryValues, writeFrame_append]
  refine WP.seq ?_
  unfold body
  refine WP.seq (VG.PPC64LE.WP.mono_syms (WP.keep [.r0] (Q := fun t' => t'.gpr .r0 = t.lr ∧ t'.mem = t.mem)
    (by prun [exec_mflr]) (by decide)) fun t' ⟨⟨h0, hm'⟩, k'⟩ hy' => ?_)
  have kk : Keep entryRegs (allocated 144 s) t' := (ku.trans kt).trans k'
  have hx' : t'.gpr .r31 = (genOfState s).F := (k'.gpr .r31 (by decide)).trans ((kt.gpr .r31 (by decide)).trans hx)
  obtain ⟨hl, hfb⟩ := gen_start hp hx' (hm'.trans hm0) kk (hy'.trans (hyt.trans hyu))
  have htsp : t'.sp = s.sp - BitVec.ofNat 64 144 := kk.sp
  have hlr : t.lr = s.lr := kt.lr.trans ku.lr
  refine WP.seq (WP.mono (gen_frame_ok v hp kk hl hfb) fun y ⟨d, hd, hy⟩ => ?_)
  subst hy
  refine WP.of_runBlock ⟨{ { d.write .r0 (t'.gpr .r0) with sp := t'.sp } with
    lr := (d.write .r0 (t'.gpr .r0)).gpr .r0 }, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mtlr], ?_⟩
  refine WP.mono (finish_ok hd rfl rfl (by
    show (d.write .r0 (t'.gpr .r0)).gpr .r31 = _
    rw [RegUpd.gpr_write, ite_eq_right (by decide)]; exact hd.1.r31))
    fun z ⟨⟨⟨hax, h31, hmz⟩, kz⟩, _⟩ => ?_
  refine ⟨done_post hp hd hax hmz, ?_, ?_, ?_⟩
  · intro r hr
    show z.gpr r = s.gpr r
    by_cases h31' : r = .r31
    · subst h31'; exact h31
    · rw [kz.gpr r (by revert r hr h31'; decide)]
      show (d.write .r0 (t'.gpr .r0)).gpr r = _
      rw [RegUpd.gpr_write, ite_eq_right (show ¬r = .r0 by revert r hr h31'; decide)]
      exact hd.1.saved r hr h31'
  · show z.sp + BitVec.ofNat 64 144 = s.sp
    rw [kz.sp]
    show t'.sp + _ = _
    rw [htsp, BitVec.sub_add_cancel]
  · show z.lr = s.lr
    rw [kz.lr]
    show (d.write .r0 (t'.gpr .r0)).gpr .r0 = s.lr
    rw [RegUpd.gpr_write_self, h0, hlr]

theorem gen_correct [InvLaw] (v : RoundImpl) (s : State) (h : genContract.pre s) :
    ∃ tr t, Exec isa (genCode v) s tr t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := gen_correct_ok v h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.PPC64LE.Generate
