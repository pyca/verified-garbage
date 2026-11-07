module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Generate.Loop
import VerifiedGarbage.Proof.Framework.AArch64.Depth
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # RSA key generation's controller on AArch64: correctness

The entry, the frame saving `x30` around the key's buffer cleared but `p` and
the loop, and the return: the contract's postcondition and the registers and
stack pointer the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Generate

open VG.Proof.RsaKeyGen.SearchFrame
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.MillerRabin.AArch64 (RoundImpl)
open VG.Impl.RsaKeyGen.AArch64.Generate
open VG.Impl.Bignum.AArch64 (st)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- The controller, with the prime search and the key it calls. -/
abbrev genCode (v : RoundImpl) : Prog isa := code (searchCall v) keyCall

/-- The return, from a state with a finished key search's memory and
regions: the octets consumed to `used`, the status, and `x19`. -/
theorem finish_ok {p : GenPublic} {original d x : State} {final : KeySearchResult}
    (h : GenDone p original final d) (hm : x.mem = d.mem) (hrd : x.rd = d.rd) (hwr : x.wr = d.wr)
    (hx19 : x.gpr .x19 = p.F) :
    WP isa (.block finish) x fun t =>
      (t.gpr .x0 = BitVec.ofNat 64 final.keyStatus ∧ t.gpr .x19 = original.gpr .x19 ∧
        t.mem = d.mem.writeW p.up (BitVec.ofNat 64 final.used)) ∧ Keep [.x0, .x1, .x2, .x19] x t := by
  obtain ⟨g, hst, -, -⟩ := h
  have hl : ∀ e, e + 8 ≤ 160 → InRegions (x.rd ++ x.wr) (p.F + BitVec.ofNat 64 e) 8 := by
    rw [hrd, hwr]; exact g.frame_ld
  have hu := g.usedScr
  have hsu0 : InRegions x.wr (p.up + BitVec.ofNat 64 0) 8 := by rw [hwr]; exact hu.st (d := 0) (by decide)
  have hsu : InRegions x.wr p.up 8 := by simpa only [BitVec.add_zero] using hsu0
  have h2 := g.header (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := g.header (j := 8) (v := BitVec.ofNat 64 final.used) (by simp [GenPublic.headers])
  have h9 : d.mem.readW (p.F + BitVec.ofNat 64 72) 64 = original.gpr .x19 := g.savedX19
  have h10 : d.mem.readW (p.F + BitVec.ofNat 64 80) 64 = BitVec.ofNat 64 final.keyStatus := hst
  simp only [Nat.reduceMul] at h2 h8
  refine WP.keep [.x0, .x1, .x2, .x19] ?_ (by decide) (by decide) (by decide +kernel)
  unfold finish
  brun [ldf, hx19, hm, hl 16 (by decide), hl 64 (by decide), hl 72 (by decide), hl 80 (by decide), h2, h8, h9,
    h10, hsu0, hsu]

theorem phase_word_if (ph : KeyPhase) :
    BitVec.ofNat 64 (phaseWord ph) = BitVec.ofNat 64 (if ph = .p then 0 else 1) := by
  cases ph <;> rfl

/-- What the controller returns, from what the loop leaves. -/
theorem done_post {p : GenPublic} {s d t : State} (hp : GenInput p s)
    (h : GenDone p s (genResult s) d)
    (hx0 : t.gpr .x0 = BitVec.ofNat 64 (genResult s).keyStatus)
    (hm : t.mem = d.mem.writeW p.up (BitVec.ofNat 64 (genResult s).used)) : genPost s t := by
  obtain ⟨g, -, hkey, req, hreq, hr⟩ := h
  have hf := hp.cfacts
  have hst := g.state
  have hkp : s.gpr .x0 = p.kp := by rw [← hp.2]; rfl
  have hup : s.gpr .x2 = p.up := by rw [← hp.2]; rfl
  have hstp : s.gpr .x7 = p.stp := by rw [← hp.2]; rfl
  have hL : genLen s = p.L := by rw [← hp.2]; rfl
  have heB : genE s = p.eB := by rw [← hp.2]; rfl
  -- The store to `used` is apart from the key's buffer and the state.
  have hfr : Frame [rU p] d.mem t.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
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
    rw [hx0, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [hkp, hL, ← hkey]
    exact hbytes (R := ⟨p.kp, 9 * p.L⟩) (.inl fun _ h => h) (by show 9 * p.L ≤ 2 ^ 64; have := hf.nK; omega)
  · rw [hup]
    show [t.mem.readW (p.up + BitVec.ofNat 64 (8 * 0)) 64] = _
    rw [Nat.mul_zero, BitVec.add_zero, hm, Mem.readW_writeW_self64]
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

/-! ## The frame saving `x30` -/

theorem iteration_depth (v : RoundImpl) : (iteration (searchCall v) keyCall).aarch64Depth = 15 := by
  have hk : VG.Impl.RsaKeyGen.AArch64.Key.code.aarch64Depth = 0 := Search.depth_of_noFrames keyCode_noFrames
  have he : exhaustedGen.aarch64Depth = 0 := rfl
  have hf : (fail 3).aarch64Depth = 0 := rfl
  have ha : afterKey.aarch64Depth = 0 := rfl
  simp only [iteration, searchRun, classify, accepted, keyRun, searchCall, keyCall, VG.Impl.Bignum.AArch64.seqs,
    Code.aarch64Depth, searchCode_depth, hk, he, hf, ha, Instr.frameUnits]
  decide

theorem F_16 (p : GenPublic) : p.F - 16 = p.sp - BitVec.ofNat 64 176 := by
  rw [GenPublic.F, BitVec.sub_sub]; rfl

/-- `p`'s slot at the start, for `q`'s search. -/
theorem start_other {p : GenPublic} {s x : State} (h : GenInput p s) (hu : GenFrame p s 0 (genProgress s) x)
    (hfu : Frame [p.frame, belowFrame s] s.mem x.mem) :
    ∀ pB, (genProgress s).phase = .q pB → Spec.Rsa.bytesAt x.mem (p.slot 4) p.L = pB := by
  have hf := h.cfacts
  obtain ⟨hL1, -, -⟩ := hf.len
  intro pB hpB
  simp only [genProgress, keyProgressAt] at hpB
  split at hpB
  · cases hpB
  · cases hpB
    have hst := hf.stack
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hst
    obtain ⟨sK, -, -, -, -⟩ := hst
    have hsub : Region.Sub ⟨p.slot 4, p.L⟩ (cK p) := slot_sub _ (by omega)
    have hk : Spec.Rsa.bytesAt x.mem (p.slot 4) p.L = Spec.Rsa.bytesAt s.mem (p.slot 4) p.L := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      refine hfu.bytes (R := ⟨p.slot 4, p.L⟩) (fun q hq => ?_) (by show p.L ≤ 2 ^ 64; have := hf.nK; omega)
        (List.mem_range.mp hi)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (hu.frame_key.sub_right hsub).symm
      · refine (sK.sub_left hsub).sub_right ?_
        show Region.Sub ⟨s.sp - BitVec.ofNat 64 stackUse, 256⟩ ⟨p.sp - BitVec.ofNat 64 416, 416⟩
        rw [h.sp_eq]
        exact Region.sub_prefix (by decide)
    rw [hk, ← h.2]
    rfl

/-- The key's buffer cleared but `p`, and the loop, from the start. -/
theorem gen_inner [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {s x : State} (h : GenInput p s)
    (hu : GenFrame p s 0 (genProgress s) x) (hfu : Frame [p.frame, belowFrame s] s.mem x.mem) :
    WP isa (.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .x .x9))) x
      (GenDone p s (genResult s)) := by
  refine WP.seq (WP.mono (clearAround_ok hu (start_other h hu hfu)) fun w ⟨hw, _⟩ => ?_)
  have hinv : GenInv p s (genResult s) (genMeasure p 0 (genProgress s)) w :=
    ⟨0, genProgress s, rfl, hw, [], by rw [consume_zero]; rw [← h.2]; rfl⟩
  exact gen_loop v hinv

/-- The frame saving `x30` writes below the controller's frame. -/
theorem push_disjoint {p : GenPublic} {s t : State} (h : GenInput p s) (htsp : t.sp = p.F)
    (hw : t.wr = p.frame :: s.wr) : ∀ R ∈ t.wr, Region.Disjoint ⟨t.sp - 16, 16⟩ R := by
  intro R hR
  rw [hw] at hR
  rw [htsp]
  rcases List.mem_cons.mp hR with rfl | hR
  · rw [F_16]
    have hs := Offset.sep_below p.sp 208 (a := 176) (n := 16) (b := 160) (k := 160) (by decide) (by decide)
      (Or.inl (by decide)) (by decide) (by decide)
    exact fun x hx hy => hs x (Nat.lt_of_succ_le (by simpa only [Region.Contains] using hx))
      (Nat.lt_of_succ_le (by simpa only [Region.Contains, GenPublic.F] using hy))
  · rw [h.1.2.2.1] at hR
    have hd := h.stack_disjoint (r := R) (List.mem_append_left _ hR)
    refine hd.sub_left ?_
    rw [F_16, h.sp_eq]
    exact Offset.sub_below s.sp (a := 176) (b := 416) (by decide) (by decide)

/-- The body, in the frame saving `x30`: the loop's end, with `x30` and the
stack pointer back. -/
theorem gen_body [Key.KeyProof] (v : RoundImpl) {p : GenPublic} {s t : State} (h : GenInput p s)
    (hx : t.gpr .x19 = p.F) (hm : t.mem = writeFrame s.mem p.F (entryValues s))
    (k : Keep [.x9, .x10, .x12, .x13, .x14, .x15, .x16, .x17, .x19] (allocated 160 s) t) :
    WP isa (body (searchCall v) keyCall) t fun u =>
      ∃ d, GenDone p s (genResult s) d ∧ u = { d.write .x .x30 (t.gpr .x30) with sp := t.sp } := by
  obtain ⟨hu, hfu⟩ := gen_start h hx hm k
  have hf := h.cfacts
  have htsp : t.sp = p.F := k.sp.trans (alloc_sp h)
  have hroom : 416 ≤ p.sp.toNat := hf.room
  have hF := h.F_toNat
  have hsp : 16 ≤ t.sp.toNat := by
    rw [htsp, hF]; exact Nat.le_sub_of_add_le (Nat.le_trans (by decide) hroom)
  unfold body
  refine WP.frameReg hsp (push_disjoint h htsp (k.wr.trans (alloc_wr h))) ?_ ?_
  · exact WP.mono (gen_inner v h hu hfu) fun d hd => ⟨d, hd, rfl⟩
  · show 16 * (Code.seq clearAround (.loop (iteration (searchCall v) keyCall) (.zero .x .x9))).aarch64Depth + 16 <
      2 ^ 64
    have hc : clearAround.aarch64Depth = 0 := rfl
    simp only [Code.aarch64Depth, iteration_depth v, hc]
    decide

/-! ## The whole controller -/

theorem gen_correct_ok [Key.KeyProof] (v : RoundImpl) {s : State} (h : genPre s) :
    WP isa (genCode v) s fun t => genPost s t ∧ abiPreserved s t := by
  have hp : GenInput (genOfState s) s := ⟨h, rfl⟩
  have hroom : 160 ≤ s.sp.toNat := Nat.le_trans (by decide) h.1
  unfold genCode code
  refine WP.alloc (by decide) hroom ?_
  simp only [VG.Impl.Bignum.AArch64.seqs]
  refine WP.seq (WP.mono (entry_ok hp) fun t ⟨⟨hx, hm⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (gen_body v hp hx hm k) fun u ⟨d, hd, hu⟩ => ?_)
  subst hu
  have g := hd.1
  have hx19 : (d.write .x .x30 (t.gpr .x30)).gpr .x19 = (genOfState s).F := by
    rw [RegUpd.gpr_write_of_ne _ _ _ (by decide)]; exact g.x19
  refine WP.mono (finish_ok hd rfl rfl rfl hx19) fun q ⟨⟨hx0, hg19, hmq⟩, kq⟩ => ?_
  refine ⟨done_post hp hd hx0 hmq, ?_, ?_, ?_⟩
  · intro reg hreg
    change q.gpr reg = s.gpr reg
    by_cases h19 : reg = .x19
    · subst h19; exact hg19
    · rw [kq.gpr reg (by revert reg hreg h19; decide)]
      show (d.write .x .x30 (t.gpr .x30)).gpr reg = _
      by_cases h30 : reg = .x30
      · subst h30
        rw [RegUpd.gpr_write_self _ _ _ _, BitVec.setWidth_eq]
        exact k.gpr .x30 (by decide)
      · rw [RegUpd.gpr_write_of_ne _ _ _ h30]
        exact g.saved reg hreg h19 h30
  · change q.sp + BitVec.ofNat 64 160 = s.sp
    rw [kq.sp]
    show t.sp + _ = _
    rw [k.sp, alloc_sp hp]
    show s.sp - _ + _ = _
    rw [BitVec.sub_add_cancel]
  · intro r hr
    exact (kq.vcs r hr).trans (g.vcs r hr)

theorem gen_correct [Key.KeyProof] (v : RoundImpl) (s : State) (h : genContract.pre s) :
    ∃ tr t, Exec isa (genCode v) s tr t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain ⟨tr, t, he, hp, ha⟩ := gen_correct_ok v h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Generate
