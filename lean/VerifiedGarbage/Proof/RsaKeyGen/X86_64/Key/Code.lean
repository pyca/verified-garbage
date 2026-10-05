import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Res
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Main
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Entry
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Implies

/-!
# An RSA key from its primes on x86-64: correctness

`code`, from a state `keyCtr` allows, ends as `keyOp` (`keyCode_wp`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Spec.Rsa (bytesAt)

theorem code_eq : code = seqs ([.block (entry ++ head)] ++
    (((loadA aPa kPp kPl ++ (loadA aQa kQp kPl ++ (loadE ++ [.block [.store (hdr kEv) .rbx]]))) ++
      (order ++ (decTo aPm aPa ++ (decTo aQm aQa ++ (lcmPart ++ ([dPart] ++ smallMask)))))) ++
    ([.ite .ne (zeros 2) keyPart] : List (Prog isa)))) := by
  simp only [code, List.append_assoc]

/-- The working space set up: `KS` from the state on entry, after `entry`
and `head`. -/
theorem keyStart_k {s : State} (c : KCtx s) :
    WP isa (.block (entry ++ head)) s fun t => KS (keyIn s) s.mem t := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have L := c.L
  have hpl : (keyIn s).pl = (s.gpr .r9).toNat := rfl
  have hpl1 := L.pl1
  have hpl2 := L.pl2
  have h256 : 8 * 32 ≤ (arg s 11).toNat * 8 := by
    have : 8 * 32 ≤ slot (keyIn s).W 16 := by unfold slot hdrBytes; omega
    omega
  rw [WP.block_append_iff]
  refine WP.mono (keyEntry_ok rfl (fun i hi => hs.st (by omega)) c.ha c.hsep) fun t₁ he => ?_
  have hs₁ := hs.congr he.keep.2.2
  have hnl : word t₁.mem (arg s 10) (8 * kNl) = BitVec.ofNat 64 (2 * (s.gpr .r9).toNat) := by
    rw [he.nl]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, c.rsi]; omega)
  refine WP.mono (keyHead_ok hs₁ he.rdi hnl (by omega) (by omega) hZ) fun t₂ ⟨hw₂, hf₂, k₂⟩ => ?_
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have hi₁ : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₁.mem := InScr.of_outside he.frame (by omega)
  have hi₂ : InScr (arg s 10) ((arg s 11).toNat * 8) t₁.mem t₂.mem := InScr.of_frm hf₂ (by
    have : 8 * sStride + 8 ≤ slot (keyIn s).W 16 := by rw [eS]; unfold slot hdrBytes; omega
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> dsimp only <;> omega)
  have hi := hi₁.trans hi₂
  have hrd : t₂.rd = s.rd := k₂.2.1.trans he.keep.2.1
  have hwr : t₂.wr = s.wr := k₂.2.2.trans he.keep.2.2
  have hA₁ : KArgs t₁.mem (keyIn s) :=
    ⟨he.no, hnl, he.dd, he.pp, he.pl.trans (BitVec.eq_of_toNat_eq (by simp [keyIn])), he.qp, he.dp, he.dq, he.qi, he.e,
      he.el.trans (BitVec.eq_of_toNat_eq (by simp [keyIn])), he.saved⟩
  refine ⟨hw₂, hA₁.congr fun i hi' => hf₂.word_eq (fun r hr => ?_) (by omega), c.p.congr hi hrd hwr,
    c.q.congr hi hrd hwr, c.e.congr hi hrd hwr, hi, hwr, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · exact (k₂.gpr (by decide)).trans (he.keep.gpr (by decide))

/-- The postcondition, from the results against `keyOp`. -/
theorem keyPost_of {s t₃ t : State} (c : KCtx s) (hi : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₃.mem)
    (R : OutsRes (keyIn s) t.mem (t.gpr .rax)) (hsv : ∀ i < 6, t.gpr (saved.getD i .rax) = (keyIn s).sv i)
    (hf : ∀ y, (keyIn s).Z ≤ ofs (keyIn s).B y →
      (∀ o ∈ outsL (keyIn s), ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = t₃.mem y)
    (hsp : t.gpr .rsp = (keyIn s).sp) :
    gprPreserved s t ∧ keyPost s t := by
  have ho : keyOuts s = outsL (keyIn s) := by simp only [keyOuts, outsL, keyIn, c.rsi]
  refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv 0 (by decide)
    · exact hsv 1 (by decide)
    · exact hsp
    · exact hsv 2 (by decide)
    · exact hsv 3 (by decide)
    · exact hsv 4 (by decide)
    · exact hsv 5 (by decide)
  · obtain ⟨hZb, hnb⟩ := c.hret b (by omega)
    rw [hf _ hZb hnb, hi _ hZb]
  · unfold keyPost keyRes
    rw [ho]
    exact R

/-- `code` computes `keyOp`. -/
theorem keyCode_wp (s : State) (h : keyPre s) : WP isa code s fun t => gprPreserved s t ∧ keyPost s t := by
  have c := keyCtx_of h
  rw [code_eq]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (keyStart_k c) fun t₁ k₁ => ?_)
  refine wp_seqs_append (by simp [loadA]) (by simp) (WP.mono (front_k k₁ c.L) fun t₃ ⟨F, hi₃⟩ => ?_)
  obtain ⟨ok, hok, hiff, hzf⟩ := F.zf
  obtain ⟨ok', hok', -, hdd⟩ := F.d
  have hoo : ok' = ok := by
    rw [hok] at hok'
    cases ok <;> cases ok' <;> first | rfl | exact absurd hok' (by decide)
  subst hoo
  have hi : InScr (arg s 10) ((arg s 11).toNat * 8) s.mem t₃.mem := k₁.inScr.trans hi₃
  refine WP.ite (decide (av (keyIn s) t₃.mem aDd ≤ 2 ^ (8 * (keyIn s).pl)) && ok') (by simp [eval, hzf])
    (fun hb => ?_) (fun hb => ?_)
  · -- `d ≤ 2^(8 pl)`: zeros, the status 2.
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨d, hd⟩ := hiff.mpr hb.2
    have hsm := hdd d hd ▸ hb.1
    exact WP.mono (zerosPart_k F.ks c.L c.O) fun t Z =>
      keyPost_of c hi (outsRes_zeros hd hsm Z) Z.2.2.1 Z.2.2.2.1 Z.2.2.2.2
  · refine WP.mono (keyPart_k F c.L c.O hok) fun t T => ?_
    have R := outsRes_tail c.L hiff hdd hb T
    obtain ⟨_, _, _, _, hsv, hf, hsp⟩ := T
    exact keyPost_of c hi R hsv hf hsp

end VG.Proof.RsaKeyGen.X86_64.Key
