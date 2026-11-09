module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Loop
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Correct
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # RSA key generation's controller on x86-64: correctness

The entry, the key's buffer cleared but `p`, the loop and the return: the
contract's postcondition, the callee-saved registers and the regions kept;
and with the stack the code uses and its return address, `genContract`'s
correctness.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Generate

open VG.Proof.RsaKeyGen.SearchFrame

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)
open VG.Proof.Ffdh.X86_64.Generation (allocated allocated_rsp allocated_reg allocated_mem freed freed_rsp
  freed_reg freed_mem frame_alloc)
open VG.Impl.RsaKeyGen.X86_64.Generate
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-- The controller, with the prime search and the key it calls. -/
abbrev genCode (v : RoundImpl) : Prog isa := code (searchCall v) keyCall

/-- The return: the octets consumed to `used`, the status, and r12. -/
theorem finish_ok {p : GenPublic} {original s : State} {final : KeySearchResult}
    (h : GenDone p original final s) :
    WP isa (.block finish) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 final.keyStatus ∧ t.gpr .r12 = original.gpr .r12 ∧
        t.mem = s.mem.writeW p.up (BitVec.ofNat 64 final.used)) ∧ Keep [.rax, .rcx, .r12] s t := by
  obtain ⟨g, hst, -, -⟩ := h
  have scr := g.scr
  have hu := g.usedScr
  have hl2 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 16) 8 := scr.ld (d := 16) (by decide)
  have hl8 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 64) 8 := scr.ld (d := 64) (by decide)
  have hl9 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 72) 8 := scr.ld (d := 72) (by decide)
  have hl10 : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 80) 8 := scr.ld (d := 80) (by decide)
  have hsu : InRegions s.wr p.up 8 := by simpa only [off, BitVec.add_zero] using hu.st (d := 0) (by decide)
  have h2 := g.header (j := 2) (v := p.up) (by simp [GenPublic.headers])
  have h8 := g.header (j := 8) (v := BitVec.ofNat 64 final.used) (by simp [GenPublic.headers])
  simp only [Nat.reduceMul] at h2 h8
  have hnF : p.F.toNat + 160 ≤ 2 ^ 64 := scr.nowrap
  have hkeep (v : BitVec 64) (d : Nat) (hd : d + 8 ≤ 160) :
      (s.mem.writeW p.up v).readW (p.F + BitVec.ofNat 64 d) 64 = s.mem.readW (p.F + BitVec.ofNat 64 d) 64 :=
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self (rU p)) v (Region.contains_self _ _)).readW
      (r := p.frame) (Offset.contains_base _ hd (by omega)) (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact g.input.frame_disjoint_writes (r := inUsed original) (by simp [inWrites]) |>.sub_right
          (by rw [g.used_region]; exact fun _ h => h)) (by decide)
  have hk9 : ∀ v : BitVec 64, (s.mem.writeW p.up v).readW (p.F + BitVec.ofNat 64 72) 64 = original.gpr .r12 :=
    fun v => (hkeep v 72 (by decide)).trans g.savedR12
  have hk10 : ∀ v : BitVec 64, (s.mem.writeW p.up v).readW (p.F + BitVec.ofNat 64 80) 64 =
      BitVec.ofNat 64 final.keyStatus := fun v => (hkeep v 80 (by decide)).trans hst
  refine WP.keep [.rax, .rcx, .r12] ?_ rfl
  unfold finish
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero,
    g.r12, hl2, hl8, hl9, hl10, hsu, h2, h8, hk9, hk10]

theorem phase_word_if (ph : KeyPhase) :
    BitVec.ofNat 64 (phaseWord ph) = BitVec.ofNat 64 (if ph = .p then 0 else 1) := by
  cases ph <;> rfl

/-- What the controller returns, from what the loop leaves. -/
theorem done_post {p : GenPublic} {s d t : State} (hp : GenInput p s)
    (h : GenDone p s (genResult s) d)
    (hax : t.gpr .rax = BitVec.ofNat 64 (genResult s).keyStatus)
    (hm : t.mem = d.mem.writeW p.up (BitVec.ofNat 64 (genResult s).used)) : genPost s t := by
  obtain ⟨g, -, hkey, req, hreq, hr⟩ := h
  have hf := hp.cfacts
  have hst := g.state
  have hkp : s.gpr .rdi = p.kp := by rw [← hp.2]; rfl
  have hup : s.gpr .rdx = p.up := by rw [← hp.2]; rfl
  have hstp : stackArg s 1 = p.stp := by rw [← hp.2]; rfl
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
    rw [hax, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
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

theorem gen_correct_ok [Key.KeyProof] (v : RoundImpl) {s : State} (h : genPre s) :
    WP isa (genCode v) s fun t => genPost s t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hp : GenInput (genOfState s) s := ⟨h, rfl⟩
  have hroom := hp.room
  have hf := hp.cfacts
  unfold genCode code
  apply frame_alloc (by decide) (by decide) (by decide) (by
    rw [← hp.sp_eq]; have : 552 ≤ (genOfState s).sp.toNat := hroom; show 160 ≤ _; omega)
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (gen_start hp) fun u ⟨hu, hfu⟩ => ?_)
  refine WP.seq (WP.mono (clearAround_ok hu ?_) fun w ⟨hw, _⟩ => ?_)
  · intro pB hpB
    simp only [genProgress, keyProgressAt] at hpB
    split at hpB
    · cases hpB
    · cases hpB
      obtain ⟨hL1, -, -⟩ := hf.len
      exact bytes_kept hfu (hu.frame_key.sub_right (slot_sub _ (by omega))) (by
        show (genOfState s).L ≤ 2 ^ 64; have := hf.nK; omega)
  have hinv : GenInv (genOfState s) s (genResult s) (genMeasure (genOfState s) 0 (genProgress s)) w :=
    ⟨0, genProgress s, rfl, hw, [], by rw [consume_zero]; rfl⟩
  refine WP.seq (WP.mono (gen_loop v hinv) fun d hd => ?_)
  refine WP.mono (finish_ok hd) fun x ⟨⟨hax, hr12, hmx⟩, k⟩ => ?_
  have g := hd.1
  have hxs : x.gpr .rsp = (genOfState s).F := by rw [k.gpr (by decide)]; exact g.rsp
  refine ⟨by rw [hxs]; exact (alloc_rsp hp).symm, by rw [k.2.2, g.wr]; exact (alloc_wr hp).symm,
    done_post hp hd (by rw [freed_reg _ _ _ (by decide)]; exact hax) (by rw [freed_mem]; exact hmx),
    fun r hr => ?_, ?_, ?_⟩
  · have hnot : r ≠ .r12 → r ∉ [Reg.rax, .rcx, .r12] := by revert r; decide
    by_cases hsp : r = .rsp
    · subst hsp
      rw [freed_rsp, hxs, ← hp.sp_eq]
      exact BitVec.sub_add_cancel _ _
    · rw [freed_reg _ _ _ hsp]
      by_cases h12 : r = .r12
      · subst h12; exact hr12
      · rw [k.gpr (hnot h12)]
        exact g.saved r hr h12 hsp
  · show x.rd = s.rd
    rw [k.2.1, g.rd]
  · show x.wr.tail = s.wr
    rw [k.2.2, g.wr]; rfl

/-! ## The code -/

private theorem code_all (q : Instr → Bool) (a b : Prog isa)
    (hp : (code (.block []) (.block [])).all q = true) (ha : a.all q = true) (hb : b.all q = true) :
    (code a b).all q = true := by
  unfold code iteration searchRun classify accepted keyRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.all, List.all_nil, ha, hb, Bool.and_true] at hp ⊢
  exact hp

private theorem code_instrs (q : Instr → Bool) (a b : Prog isa)
    (hp : (code (.block []) (.block [])).allInstrs q = true) (ha : a.allInstrs q = true)
    (hb : b.allInstrs q = true) : (code a b).allInstrs q = true := by
  unfold code iteration searchRun classify accepted keyRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.allInstrs, ha, hb, Bool.and_true] at hp ⊢
  exact hp

private theorem code_ctlC (a b : Prog isa) (hp : ctlC (code (.block []) (.block [])) = true)
    (ha : ctlC a = true) (hb : ctlC b = true) : ctlC (code a b) = true := by
  unfold code iteration searchRun classify accepted keyRun at hp ⊢
  simp only [VG.Impl.Bignum.X86_64.seqs, ctlC, ha, hb, Bool.and_true] at hp ⊢
  exact hp

theorem keyCode_sp : VG.Impl.RsaKeyGen.X86_64.Key.code.all (fun i => !isa.writesSp i) = true := by
  decide +kernel

theorem genCode_sp (v : RoundImpl) : (genCode v).all (fun i => !isa.writesSp i) = true :=
  code_all _ _ _ (by decide +kernel) (Search.searchCode_sp v) keyCode_sp

/-- Key generation loads MXCSR only where the round restores it. -/
theorem genCode_ctlC (v : RoundImpl) : ctlC (genCode v) = true :=
  code_ctlC _ _ (by decide +kernel) (ctlOk_of_ctlC (Search.searchCode_ctlC v)) (ctlOk_of_noLoad keyCode_mx)

theorem keyCode_x86_64Depth : VG.Impl.RsaKeyGen.X86_64.Key.code.x86_64Depth = 0 :=
  x86_64Depth_zero keyCode_noSp keyCode_depth

theorem genCode_depth (v : RoundImpl) : (genCode v).x86_64Depth ≤ stackUse := by
  have hs := Search.searchCode_depth v
  have hk := keyCode_x86_64Depth
  have hc : clearAround.x86_64Depth = 0 := rfl
  have he : exhaustedGen.x86_64Depth = 0 := rfl
  have hf : (fail 3).x86_64Depth = 0 := rfl
  have ha : afterKey.x86_64Depth = 0 := rfl
  unfold genCode code iteration searchRun classify accepted keyRun searchCall keyCall
  simp only [VG.Impl.Bignum.X86_64.seqs, Code.x86_64Depth, Instr.frameBytes, frameBytes, hk, hc, he, hf, ha,
    Nat.zero_max, Nat.max_zero, Nat.zero_add]
  have hs' : (Search.searchCode v).x86_64Depth ≤ 336 := hs
  exact Nat.add_le_of_le_sub (by decide) (Nat.max_le.mpr ⟨by show _ ≤ 392; omega, by decide⟩)

theorem gen_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : genPre s) (he : Exec isa (genCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨-, -, -, hwr, -, -, -, hstk, -⟩ := h
  have hd : (genCode v).x86_64Depth ≤ 552 := genCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (genCode_sp v)) he (by omega)
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    exact (hstk r (List.mem_append_left _ hr)).1
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega)

theorem gen_correct [Key.KeyProof] (v : RoundImpl) (s : State) (h : genContract.pre s) :
    ∃ tr t, Exec isa (genCode v) s tr t ∧ abiPreserved s t ∧ genContract.post s t := by
  obtain ⟨tr, t, he, hp, hg, _, _⟩ := gen_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_ctl (ctlOk_of_ctlC (genCode_ctlC v)) he ⟨hg, gen_return_address v h he⟩, hp⟩

end VG.Proof.RsaKeyGen.X86_64.Generate
