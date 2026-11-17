module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Loop
import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
meta import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Generate.Loop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyInit

/-! # The controller is correct (i686)

The push, the entry, the key's buffer cleared, the loop, the results
(`used`, `results_ok`) and the registers restored (`restore_ok`): the
contract's postcondition (`correct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Generate

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Generate
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen
open VG.Proof.RsaKeyGen.KeySearch

/-! ## The code never writes `esp` but by its frames -/

theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi =>
  (List.mem_append.mp hi).elim (ha i) (hb i)
theorem noSp_ite {c : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite c a b) := fun i hi =>
  (List.mem_append.mp hi).elim (ha i) (hb i)
theorem noSp_loop {c : Cond} {a : Prog isa} (ha : NoSp a) : NoSp (.loop a c) := ha
theorem noSp_alloc {k : Nat} {a : Prog isa} (ha : NoSp a) : NoSp (.frame (.alloc k) a (.free k)) := fun i hi => by
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact ha i hi
  · rfl
theorem noSp_block {is : List Instr} (h : is.all (fun i => !Taint.clobbers i .esp) = true) : NoSp (.block is) :=
  fun i hi => by simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi

theorem body_noSp' (srch : Srch) (key : KeyImpl) : NoSp (body srch.call key.call) := by
  obtain hz : NoSp zeroLoop := noSp_loop (noSp_block (by decide))
  obtain hca : NoSp clearAll := noSp_seq (noSp_block (by decide)) hz
  obtain hf3 : NoSp (fail 3) := noSp_seq hca (noSp_block (by decide))
  obtain hf2 : NoSp (fail 2) := noSp_seq hca (noSp_block (by decide))
  obtain hn0 : NoSp (.block (nextPrime 0)) := noSp_block (by decide)
  obtain hn1 : NoSp (.block (nextPrime 1)) := noSp_block (by decide)
  obtain hex : NoSp exhaustedGen := noSp_seq (noSp_block (by decide)) (noSp_ite hf3
    (noSp_block (by decide)))
  obtain hak : NoSp afterKey := noSp_seq (noSp_block (by decide)) (noSp_ite (noSp_block (by decide))
    (noSp_seq (noSp_block (by decide)) (noSp_ite hn0 hf2)))
  obtain hkr : NoSp (keyRun key.call) := noSp_alloc (kbody_noSp key)
  obtain hacc : NoSp (accepted key.call) := noSp_seq (noSp_block (by decide)) (noSp_ite hn1 (noSp_seq hkr hak))
  obtain hcl : NoSp (classify key.call) := noSp_seq (noSp_block (by decide)) (noSp_ite (noSp_block (by decide))
    (noSp_seq (noSp_block (by decide)) (noSp_ite hex (noSp_seq (noSp_block (by decide)) (noSp_ite hf3 hacc)))))
  obtain hsr : NoSp (searchRun srch.call) := noSp_alloc (body_noSp srch)
  obtain hit : NoSp (iteration srch.call key.call) := noSp_seq hsr (noSp_seq hcl (noSp_block (by decide)))
  obtain hclr : NoSp clearAround := noSp_seq (noSp_seq (noSp_block (by decide)) hz) (noSp_seq (noSp_block (by decide)) hz)
  exact noSp_seq (noSp_block (by decide)) (noSp_seq hclr (noSp_seq (noSp_loop hit) (noSp_block (by decide))))

/-! ## The results and the registers restored -/

/-- The octets consumed, to `used` as two halves, and the status to `eax`. -/
theorem results_ok {p : GenPublic} {o s : State} {used : Nat} {st : KeyProgress} (h : GenFrame p o used st s) :
    WP isa (.block results) s fun t =>
      (t.gpr .eax = s.gpr .ebx ∧ t.mem.readW ((arg o 2).setWidth 64 + BitVec.ofNat 64 0) 32 = s.gpr .esi ∧
        t.mem.readW ((arg o 2).setWidth 64 + BitVec.ofNat 64 4) 32 = 0 ∧ Frame [uR o] s.mem t.mem) ∧
        Keep [.eax, .ecx, .edx] s t ∧ t.syms = s.syms := by
  have hb := h.toGenBase
  have hi := hb.input
  have A := hi.abi
  have WU (k : Nat) (hk : k < 8) : (arg o 2 + BitVec.ofNat 32 k).setWidth 64 = (arg o 2).setWidth 64 + BitVec.ofNat 64 k :=
    VG.Proof.MlKem.X86.ea_off (by have := A.uBound; omega_using [hk, this])
  have WUi (k : Nat) (hk : k + 4 ≤ 8) : InRegions s.wr ((arg o 2).setWidth 64 + BitVec.ofNat 64 k) 4 :=
    ⟨uR o, by rw [hb.wr, A.wr]; simp, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  refine WP.blockKeep _ ?_ (by rfl)
  simp only [results, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 2) (d := 28) rfl, hb.arg_in (i := 2) (by decide),
    hb.arg_val (i := 2) (by decide), WU 0 (by decide), WU 4 (by decide), WUi 0 (by decide), WUi 4 (by decide)]
  refine ⟨by simp (disch := decide) only [rdS, rdN], by simp only [rdS], ?_⟩
  have hu := A.uBound
  refine Frame.writeW (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ ?_) (List.mem_singleton_self _) _ ?_
  · exact Offset.contains_base _ (by decide) (by decide)
  · exact Offset.contains_base _ (by decide) (by decide)

/-- The callee-saved registers but `ebx`, from the frame. -/
theorem restore_ok {p : GenPublic} {o s : State} (hi : GenInput p o) (hsp : s.gpr .esp = p.S1)
    (hw : below p.sp 16 ∈ s.wr) (hs : Saved s.mem p.S1 o) :
    WP isa (.block Impl.Mont.X86.Compact.restoreRegs) s fun t =>
      (t.gpr .edi = o.gpr .edi ∧ t.gpr .esi = o.gpr .esi ∧ t.gpr .ebp = o.gpr .ebp ∧ t.mem = s.mem) ∧
        Keep [.edi, .esi, .ebp] s t ∧ t.syms = s.syms := by
  have A := hi.abi
  obtain pe := push_eq hi
  have r (d : Nat) (hd : d + 4 ≤ 16) : InRegions (s.rd ++ s.wr) ((p.S1 + BitVec.ofNat 32 d).setWidth 64) 4 := by
    refine ⟨_, List.mem_append_right _ hw, ?_⟩
    rw [pe]
    obtain e := addr_sub A (k := 16) (d := d) (by decide) (by omega_using [hd])
    rw [show (p.S1 + BitVec.ofNat 32 d).setWidth 64 = addr (o.gpr .esp - BitVec.ofNat 32 16) d by
      rw [GenPublic.S1, hi.sp_eq]; rfl, e]
    exact Offset.contains _ (by omega_using []) (by omega_using [hd]) (by omega_using [])
  obtain ⟨s0, s1, s2, -⟩ := hs
  refine WP.blockKeep _ ?_ (by rfl)
  unfold Impl.Mont.X86.Compact.restoreRegs
  xrun [State.ea, at_, hsp, r 0 (by decide), r 4 (by decide), r 8 (by decide), s0, s1, s2]

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

/-- The key search from the progress on entry. -/
abbrev genResult (o : State) : KeySearchResult := keySearch (genLen o) (genE o) (genProgress o) (genRand o)

theorem gen_correct_ok (srch : Srch) (key : KeyImpl) {o : State} (h : contract.pre o) :
    WP isa (code srch.call key.call) o fun t => abiPreserved o t ∧ contract.post o t := by
  let p := genOfState o
  obtain hp : GenInput p o := ⟨h, rfl⟩
  have A := hp.abi
  have hv := hp.len_valid
  have h1 : 284 ≤ (o.gpr .esp).toNat := A.stackLow
  have postLocal : ∀ t m (uu : Nat → BitVec 32), abiPreserved o t ∧ contract.post o t →
      Frame [below (o.gpr .esp) (4 * pushRegs.length)] t.mem m →
      abiPreserved o { t with mem := m, unknowns := uu } ∧ contract.post o { t with mem := m, unknowns := uu } := by
    intro t m uu ⟨abi, post⟩ fl
    refine ⟨VG.Proof.Mont.X86.Compact.abi_frame (by omega_using [h1]) abi fl, ?_⟩
    have Ps : Region.Sub ⟨low o + BitVec.ofNat 64 268, 16⟩ (lowR o) := low_sub (by decide)
    have hK := hp.kR_eq ▸ A.lowK
    rw [show below (o.gpr .esp) (4 * pushRegs.length) = ⟨low o + BitVec.ofNat 64 268, 16⟩ from push_eq hp] at fl
    sig_post [contract, Spec.RsaKeyGen.keySearchContract, Spec.RsaKeyGen.keySearchSig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at post
    sig_post [contract, Spec.RsaKeyGen.keySearchContract, Spec.RsaKeyGen.keySearchSig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
    obtain ⟨q1, q2, q3, req, q4, q5, q6⟩ := post
    refine ⟨q1, ?_, ?_, req, ?_, ?_, q6⟩
    · rw [VG.Proof.Rsa.rsa_bytes_frame fl ?f1 ?d1]
      · exact q2
      · change 9 * p.L < 2 ^ 64; have := hp.kBound'; omega_using [this]
      · intro r hr; rw [List.mem_singleton.mp hr]; exact (hK.sub_left Ps).symm
    · rw [VG.Proof.Rsa.wordsAt_frame fl ?f2 ?d2]
      · exact q3
      · decide
      · intro r hr; rw [List.mem_singleton.mp hr]; exact (A.lowU.sub_left Ps).symm
    · rw [VG.Proof.Rsa.wordsAt_frame fl ?f3 ?d3]
      · exact q4
      · decide
      · intro r hr; rw [List.mem_singleton.mp hr]
        exact ((A.lowS.sub_right (Region.sub_prefix (by decide))).sub_left Ps).symm
    · rw [VG.Proof.Rsa.rsa_bytes_frame fl ?f4 ?d4]
      · exact q5
      · decide
      · intro r hr; rw [List.mem_singleton.mp hr]
        exact ((A.lowS.sub_right (Offset.sub_base (d := 48) (n := 8) (k := 56) _ (by decide))).sub_left Ps).symm
  unfold code
  refine WP.frameLocal (rs := pushRegs) (r := .ebx) (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega_using [h1]) (body_noSp' srch key) postLocal ?_
  unfold body
  refine WP.seq (WP.mono (entry_ok hp) fun s1 ⟨f1, hbx1, hm1⟩ => ?_)
  refine WP.seq (WP.mono (clearAround_ok f1 hbx1 ?other) fun s2 h2 => ?_)
  case other =>
    intro pB hph
    simp only [genProgress, keyProgressAt] at hph
    split at hph
    · cases hph
    · injection hph with hph'
      subst hph'
      rw [hm1]
      obtain hf := pushed_frame (rs := pushRegs) (s := o) (by decide)
        (by simp only [List.length_cons, List.length_nil]; omega_using [h1])
      obtain hk : Region.Sub ⟨p.slot 4, p.L⟩ (kR o) := by
        rw [hp.kR_eq]; exact Offset.sub_base _ (by omega_using [])
      exact bytes_keep (R := ⟨p.slot 4, p.L⟩) hf (fun q hq => by
        obtain rfl := List.mem_singleton.mp hq
        exact (A.lowK.symm.sub_left hk).sub_right (by rw [hp.low_eq]; exact below_sub (by decide) A.stackLow))
        (show p.L ≤ 2 ^ 64 by omega_using [hv])
  obtain hinv : GenInv p o (tailOf p o 0 (genProgress o)) (genMeasure p 0 (genProgress o)) s2 :=
    ⟨0, _, rfl, h2.1, [], (consume_zero _).symm⟩
  refine WP.seq (WP.mono (gen_loop srch key hinv) fun s3 hd => ?_)
  obtain ⟨g3, hbx3, hkey3, req3, hw3, hr3⟩ := hd
  unfold finish
  refine WP.block_append (WP.mono (results_ok g3) fun s4 ⟨⟨ha4, hlo, hhi, fr4⟩, k4, sy4⟩ => ?_)
  obtain Ps : Region.Sub ⟨low o + BitVec.ofNat 64 268, 16⟩ (lowR o) := low_sub (by decide)
  obtain hb4 : GenBase p o s4 := g3.toGenBase.keep k4 (by decide) sy4
    (saved_frame hp (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.lowU.sub_left Ps) fr4 g3.saved)
    (fr4.sub fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact ⟨uR o, by simp [changes], fun _ h => h⟩)
  refine WP.mono (restore_ok hp hb4.sp (by rw [hb4.wr]; exact List.mem_cons_self ..) hb4.saved)
    fun s5 ⟨⟨hdi, hsi, hbp, hm5⟩, k5, sy5⟩ => ?_
  obtain sp5 : s5.gpr .esp = p.S1 := (k5.gpr (by decide)).trans hb4.sp
  obtain ax5 : s5.gpr .eax = BitVec.ofNat 32 (tailOf p o 0 (genProgress o)).keyStatus :=
    (k5.gpr (by decide)).trans (ha4.trans hbx3)
  obtain retL : (retR o).Disjoint (lowR o) := Offset.base_disjoint_below _ (by decide)
  change abiPreserved o (popped .ebx 4 s5) ∧ contract.post o (popped .ebx 4 s5)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [popped_four_value, sp5, hm5]; exact hb4.saved.2.2.2
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact hsi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact hdi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact hbp
    · rw [popped_esp, sp5, GenPublic.S1]
      change p.sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 16 = _
      rw [BitVec.sub_add_cancel]; rfl
  · rw [popped_mem, hm5]
    refine (hb4.frame).readW (r := retR o) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [A.retK, A.retU, A.retB, A.retS, by rw [← hp.low_eq]; exact retL]
  · sig_post [contract, Spec.RsaKeyGen.keySearchContract, Spec.RsaKeyGen.keySearchSig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
    obtain eK : keySearch (genLen o) (genE o)
        (keyProgressAt o.mem ((arg o 0).setWidth 64) ((arg o 7).setWidth 64) (genLen o)) (genRand o) =
        tailOf p o 0 (genProgress o) := by simp only [tailOf, List.drop_zero]; rfl
    rw [eK]
    obtain hlt := keyStatus_lt (tailOf p o 0 (genProgress o))
    have hul := g3.used_le
    have hrl := hp.randLen_lt
    have m5 : s5.mem = s4.mem := hm5
    have hst := g3.state
    have sU : (sR o).Disjoint (uR o) := A.us.symm
    have wk (d : Nat) (hd : d + 8 ≤ 56) : word s5.mem p.stp d = word s3.mem p.stp d := by
      rw [m5]
      exact word_keep fr4 fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact sU.sub_left (by rw [hp.sR_eq]; exact Offset.sub_base _ hd)
    refine ⟨?_, ?_, ?_, req3, ?_, ?_, hr3⟩
    · rw [BitVec.setWidth_append_eq_right, ax5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlt])]
    · rw [m5]
      have := bytes_keep (R := ⟨p.kp.setWidth 64, 9 * p.L⟩) fr4 (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; rw [← hp.kR_eq]; exact A.ku) (show 9 * p.L ≤ 2 ^ 64 by omega_using [hv])
      exact this.trans hkey3
    · simp only [Spec.Rsa.wordsAt, show List.range 1 = [0] from rfl, List.map_cons, List.map_nil, Nat.mul_zero]
      rw [m5, word_halves (d := 0) hlo hhi, g3.esi, zero_app (by omega_using [hul, hrl])]
    · simp only [Spec.Rsa.wordsAt, show List.range 6 = [0, 1, 2, 3, 4, 5] from rfl, List.map_cons, List.map_nil,
        Nat.reduceMul]
      obtain hph : ∀ ph : KeyPhase, (if ph = KeyPhase.p then 0 else 1) = phaseWord ph := by
        intro ph; cases ph <;> rfl
      simp only [List.cons.injEq, and_true, hph]
      exact ⟨(wk 0 (by decide)).trans hst.remaining, (wk 8 (by decide)).trans hst.len,
        (wk 16 (by decide)).trans hst.cap, (wk 24 (by decide)).trans hw3, (wk 32 (by decide)).trans hst.phase,
        (wk 40 (by decide)).trans hst.left⟩
    · rw [m5]
      refine (bytes_keep (R := ⟨p.stp.setWidth 64 + 48, 8⟩) fr4 (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact sU.sub_left (by rw [hp.sR_eq]; exact Offset.sub_base (d := 48) (n := 8) (k := 56) _ (by decide)))
        (show 8 ≤ 2 ^ 64 by decide)).trans hst.e

theorem correct (srch : Srch) (key : KeyImpl) (s : State) (h : contract.pre s) :
    ∃ trace t, Exec isa (code srch.call key.call) s trace t ∧ abiPreserved s t ∧ contract.post s t := by
  obtain ⟨tr, t, he, ha, hp⟩ := gen_correct_ok srch key h
  exact ⟨tr, t, he, ha, hp⟩

end VG.Proof.RsaKeyGen.X86.Generate
