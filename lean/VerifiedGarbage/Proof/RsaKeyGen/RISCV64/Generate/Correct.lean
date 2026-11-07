module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Generate.Loop
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # RSA key generation's controller on RISC-V: correctness

The entry in the frame of 112 bytes, the frame saving `ra` with the key's
buffer cleared but `p` and the loop in it, and the return: the contract's
postcondition and what the calling convention preserves.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.RISCV64 VG.Proof.Bignum VG.Proof.Bignum.RISCV64
open VG.Impl.RsaKeyGen.RISCV64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch
open VG.Proof.Rsa.RISCV64 (InvLaw)
open VG.Proof.MillerRabin.RISCV64 (RoundImpl)
open VG.Proof.RsaKeyGen.RISCV64.Search (WP.keepS KeepS)

/-- The controller, with the prime search and the key it calls. -/
abbrev genCode (v : RoundImpl) : Prog isa := code (searchCall v) keyCall

/-- The return: the octets consumed to `used`, the status, and `s0`. -/
theorem finish_ok {p : GenPublic} {original d y : State} {final : KeySearchResult}
    (g : GenDone p original final d) (hm : y.mem = d.mem) (hw : y.wr = d.wr) (h31 : y.gpr .s0 = p.F) :
    WP isa (.block finish) y fun t =>
      ((t.gpr .a0 = BitVec.ofNat 64 final.keyStatus ∧ t.gpr .s0 = original.gpr .s0 ∧
        t.mem = y.mem.writeW (p.up + BitVec.ofNat 64 0) (BitVec.ofNat 64 final.used)) ∧
        KeepS [.a0, .a2, .a3, .s0] y t) ∧ t.syms = y.syms := by
  obtain ⟨g, hst, -, -⟩ := g
  have hyw : y.wr = p.frame :: original.wr := hw.trans g.wr
  have scr := g.input.frame_scr hyw
  have hl : ∀ d, d + 8 ≤ 112 → InRegions (y.rd ++ y.wr) (p.F + BitVec.ofNat 64 d) 8 :=
    fun d hd => let ⟨r, hr, hc⟩ := scr.st hd; ⟨r, List.mem_append_right _ hr, hc⟩
  have hus : Scr y p.up 8 := by
    have hn := g.input.nowrap (r := inUsed original) (by simp [inWrites])
    rw [g.used_region] at hn
    have ha : p.up.toNat % 8 = 0 := by rw [← g.input.2]; exact g.input.used_al
    refine Scr.of_mem ?_ hn ha
    rw [hyw, g.input.wr_eq, ← g.used_region]
    simp [inWrites]
  have hsu : InRegions y.wr (p.up + BitVec.ofNat 64 0) 8 := hus.st (d := 0) (n := 8) (by decide)
  have hau : (p.up + BitVec.ofNat 64 0).toNat % 8 = 0 := hus.al8 (d := 0) (by decide) (by decide)
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
  have h9 : y.mem.readW (p.F + BitVec.ofNat 64 72) 64 = original.gpr .s0 := by rw [hm]; exact g.savedS0
  have h10 : y.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 final.keyStatus := by rw [hm]; exact hst
  have hk9 : ∀ v : BitVec 64, (y.mem.writeW (p.up + BitVec.ofNat 64 0) v).readW (p.F + BitVec.ofNat 64 72) 64 =
      original.gpr .s0 := fun v => (hkeep v 72 (by decide)).trans h9
  have hk10 : ∀ v : BitVec 64, (y.mem.writeW (p.up + BitVec.ofNat 64 0) v).readW (p.F + BitVec.ofNat 64 80) 64 =
      BitVec.ofNat 64 final.keyStatus := fun v => (hkeep v 80 (by decide)).trans h10
  refine WP.keepS [.a0, .a2, .a3, .s0] ?_ (by decide +kernel)
  unfold finish
  brun [ldf, h31, hl 16 (by decide), hl 64 (by decide), hl 72 (by decide), hl 80 (by decide),
    scr.al8 (d := 16) (by decide) (by decide), scr.al8 (d := 64) (by decide) (by decide),
    scr.al8 (d := 72) (by decide) (by decide), scr.al8 (d := 80) (by decide) (by decide), hsu, hau, h2, h8,
    hk9, hk10]

theorem phase_word_if (ph : KeyPhase) :
    BitVec.ofNat 64 (phaseWord ph) = BitVec.ofNat 64 (if ph = .p then 0 else 1) := by
  cases ph <;> rfl

/-- What the controller returns, from what the loop leaves. -/
theorem done_post {p : GenPublic} {s d t : State} (hp : GenInput p s)
    (h : GenDone p s (genResult s) d)
    (hax : t.gpr .a0 = BitVec.ofNat 64 (genResult s).keyStatus)
    (hm : t.mem = d.mem.writeW (p.up + BitVec.ofNat 64 0) (BitVec.ofNat 64 (genResult s).used)) :
    genPost s t := by
  obtain ⟨g, -, hkey, req, hreq, hr⟩ := h
  have hf := hp.cfacts
  have hst := g.state
  have hkp : s.gpr .a0 = p.kp := by rw [← hp.2]; rfl
  have hup : s.gpr .a2 = p.up := by rw [← hp.2]; rfl
  have hstp : s.gpr .a7 = p.stp := by rw [← hp.2]; rfl
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


theorem iteration_sdepth (v : RoundImpl) : sdepth (iteration (searchCall v) keyCall) ≤ 528 := by
  have := search_sdepth v
  have hk := keyCode_sdepth
  simp only [iteration, seqs, searchRun, searchCall, classify, accepted, keyRun, keyCall, exhaustedGen, fail,
    afterKey, clearAll, clear, Impl.Bignum.RISCV64.countLoop, sdepth, Instr.frameBytes, Search.searchCode, hk]
  omega

theorem clearAround_sdepth : sdepth clearAround = 0 := by
  simp only [clearAround, seqs, clear, Impl.Bignum.RISCV64.countLoop, sdepth, Nat.max_self]

/-- The key's buffer cleared but `p`, and the loop. -/
theorem gen_body_ok [InvLaw] (v : RoundImpl) {s t' : State} (hp : GenInput (genOfState s) s)
    (hl : GenFrame (genOfState s) s 0 (genProgress s) (framed .ra t'))
    (hfb : Frame [below s.sp stackUse] s.mem (framed .ra t').mem) :
    WP isa (.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .a6))) (framed .ra t')
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

theorem F_16_sp (s : State) : (genOfState s).F - 16 = s.sp - BitVec.ofNat 64 128 := by
  rw [GenPublic.F, BitVec.sub_sub]; rfl

/-- The frame saving `ra`, around the body. -/
theorem gen_frame_ok [InvLaw] (v : RoundImpl) {s t' : State} (hp : GenInput (genOfState s) s)
    (kk : KeepS entryRegs (allocd 112 s) t')
    (hl : GenFrame (genOfState s) s 0 (genProgress s) (framed .ra t'))
    (hfb : Frame [below s.sp stackUse] s.mem (framed .ra t').mem) :
    WP isa (body (searchCall v) keyCall) t' fun y => ∃ d, GenDone (genOfState s) s (genResult s) d ∧
        y = { d.write .ra (t'.gpr .ra) with sp := t'.sp } := by
  have hroom := hp.room
  have hsp0 : (genOfState s).sp = s.sp := hp.sp_eq
  have hsu : stackUse = 656 := rfl
  have hroom' : stackUse ≤ s.sp.toNat := by rw [← hsp0]; exact hroom
  have htsp : t'.sp = (genOfState s).F := kk.sp.trans (alloc_sp hp)
  have hsp16 : 16 ≤ t'.sp.toNat := by rw [htsp, hp.F_toNat, hsp0]; omega
  unfold body
  refine Search.WP.frameRegAny hsp16 ?_ (WP.mono (gen_body_ok v hp hl hfb) fun d hd => ⟨d, hd, rfl⟩) (by
    have := iteration_sdepth v
    simp only [sdepth, clearAround_sdepth]
    omega)
  intro R hR
  rw [kk.wr, alloc_wr hp] at hR
  rw [htsp, F_16_sp]
  rcases List.mem_cons.mp hR with rfl | hR
  · rw [← hsp0]
    have hs := Offset.sep_below (genOfState s).sp 656 (a := 128) (n := 16) (b := 112) (k := 112) (by decide)
      (by decide) (Or.inl (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (Nat.lt_of_succ_le (by simpa only [Region.Contains] using hx))
      (Nat.lt_of_succ_le (by simpa only [Region.Contains, GenPublic.frame, GenPublic.F] using hy))
  · rw [hp.wr_eq] at hR
    have hd := hp.stack_disjoint (r := R) (List.mem_append_left _ hR)
    exact hd.sub_left (Offset.sub_below s.sp (a := 128) (b := stackUse) (by decide) (by decide))

theorem gen_correct_ok [InvLaw] (v : RoundImpl) {s : State} (h : genPre s) :
    WP isa (genCode v) s fun t => genPost s t ∧ abiPreserved s t := by
  have hp : GenInput (genOfState s) s := ⟨h, rfl⟩
  have hroom := hp.room
  have hsp0 : (genOfState s).sp = s.sp := hp.sp_eq
  have hsu : stackUse = 656 := rfl
  have hroom' : stackUse ≤ s.sp.toNat := by rw [← hsp0]; exact hroom
  unfold genCode code
  refine WP.alloc (by decide) (by show 112 ≤ s.sp.toNat; omega) ?_
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (VG.RISCV64.WP.mono_syms (entryHead_ok hp) fun u ⟨⟨hx, hmu⟩, ku⟩ hyu =>
    VG.RISCV64.WP.mono_syms (entryWords_ok hp hx hmu ku) fun t ⟨hmt, kt⟩ hyt => ?_))
  have hm0 : t.mem = writeFrame s.mem (genOfState s).F (entryValues s) := by
    rw [hmt, hmu, entryValues, writeFrame_append]
  have kk : KeepS entryRegs (allocd 112 s) t := ku.trans kt
  have hx' : t.gpr .s0 = (genOfState s).F := (kt.gpr .s0 (by decide)).trans hx
  obtain ⟨hl, hfb⟩ := gen_start hp hx' hm0 kk (hyt.trans hyu)
  have htsp : t.sp = (genOfState s).F := kk.sp.trans (alloc_sp hp)
  have hra : t.gpr .ra = s.gpr .ra := kk.gpr .ra (by decide)
  refine WP.seq (WP.mono (gen_frame_ok v hp kk hl hfb) fun y ⟨d, hd, hy⟩ => ?_)
  subst hy
  refine WP.mono (finish_ok hd rfl rfl (by
    show (d.write .ra (t.gpr .ra)).gpr .s0 = _
    rw [RegUpd.gpr_write, ite_eq_right (by decide)]; exact hd.1.s0))
    fun z ⟨⟨⟨hax, h31, hmz⟩, kz⟩, _⟩ => ?_
  refine ⟨done_post hp hd hax hmz, ?_, ?_, ?_⟩
  · intro r hr
    show z.gpr r = s.gpr r
    by_cases h31' : r = .s0
    · subst h31'; exact h31
    · rw [kz.gpr r (by revert r hr h31'; decide)]
      show (d.write .ra (t.gpr .ra)).gpr r = _
      rw [RegUpd.gpr_write, ite_eq_right (show ¬r = .ra by revert r hr h31'; decide)]
      exact hd.1.saved r hr h31'
  · show z.sp + BitVec.ofNat 64 112 = s.sp
    rw [kz.sp]
    show t.sp + _ = _
    rw [htsp, ← hsp0, GenPublic.F, BitVec.sub_add_cancel]
  · show z.gpr .ra = s.gpr .ra
    rw [kz.gpr .ra (by decide)]
    show (d.write .ra (t.gpr .ra)).gpr .ra = s.gpr .ra
    rw [RegUpd.gpr_write_self, hra]

theorem gen_correct [InvLaw] (v : RoundImpl) (s : State) (h : genContract.pre s) :
    ∃ tr t, Exec isa (genCode v) s tr t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := gen_correct_ok v h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.RISCV64.Generate
