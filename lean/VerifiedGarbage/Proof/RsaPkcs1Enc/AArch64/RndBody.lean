module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndReject
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndFrame
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndSetup
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndCall
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndInvoke
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndTail

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: correctness

With `PS` full, the call and its tail (`accept_ok`); the frames' body
(`body_ok`); and the function (`code_ok`): the registers the ABI keeps and
`post`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.RsaPkcs1Sig.AArch64 (PdChecked)

/-- `PS` full after `i` octets: the state before the call's arguments. -/
theorem ready_of {P : Nat} {s t₀ u : State} (hp : RPre P s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hf : (kept s i).length = psLen s) : Ready s u i (kept s i) := by
  have hP := hp.ps
  refine ⟨hI.fr, (hb.keep.trans hI.keep).mono (by decide), hI.x12,
    (hI.keep .x15 (by decide)).trans hb.x15, hf, ?_, hI.hi⟩
  rw [← hf]
  simp only [Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp)
  intro j h₁ _
  simp only [List.length_map, List.length_range] at h₁
  simp only [List.getElem_map, List.getElem_range]
  rw [show off (Q s) oBuf + BitVec.ofNat 64 j = off (Q s) (oBuf + j) from off_off _ _ _, hI.buf j h₁]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

theorem accept_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s t₀ u : State} (hp : RPre c.stack s) (hb : Before s t₀) {i : Nat}
    (hI : At s t₀ i u) (hf : (kept s i).length = psLen s)
    (hpre : Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) :
    WP isa (accept (encName c) (encCode c)) u fun x => Fin c.stack s x ∧ post s x := by
  have hr := ready_of hp hb hI hf
  refine WP.seq (WP.mono (args_ok hp hr) fun w ha => ?_)
  refine WP.seq (WP.mono (call_ok c hsat hp ha) fun u' hac => ?_)
  refine WP.mono (accTail_ok hp hac) fun x ⟨hfin, ht0, ht1, hres⟩ => ⟨hfin, ?_⟩
  obtain ⟨ho, hu⟩ := VG.Proof.RsaPkcs1Enc.padSearch_accepted hpre
  show (∃ req, _ ∧ _ ∧ _) ∧ _
  unfold Spec.Entropy.Result.Requests
  rw [ho, hu]
  exact ⟨⟨0, ht0, ht1, rfl⟩, hres⟩

theorem body_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s : State} (hp : RPre c.stack s) :
    WP isa (body (encName c) (encCode c)) (entered s) fun x => Fin c.stack s x ∧ post s x := by
  have hP := hp.ps
  refine WP.seq (WP.mono (setup_ok hp) fun t₀ hb => ?_)
  refine WP.seq (WP.mono (scan_ok hp hb) fun u ⟨i, hI, hd⟩ => ?_)
  have hc := hI.hc
  rcases hd with ⟨hf, hpre⟩ | ⟨rfl, hlt⟩
  · refine WP.ite true (by rw [eval_zero, hI.x16, hf, Nat.sub_self]; rfl) (fun _ => accept_ok c hsat hp hb hI hf hpre)
      (fun h => absurd h (by decide))
  · have hne : (BitVec.ofNat 64 (psLen s - (kept s (stackArg s 2).toNat).length) == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine WP.ite false (by rw [eval_zero, hI.x16, hne]) (fun h => absurd h (by decide))
      (fun _ => reject_ok hp hb hI hlt)

theorem popped_gpr (s : State) (r : Reg) :
    (popped .x30 s).gpr r = if r = .x30 then s.mem.read s.sp 8 else s.gpr r := by
  show (s.write .x .x30 _).gpr r = _
  rw [RegUpd.gpr_write, BitVec.setWidth_eq]

theorem post_congr {s x y : State} (hm : y.mem = x.mem) (h0 : y.gpr .x0 = x.gpr .x0) (h : post s x) :
    post s y := by
  unfold post; rw [hm, h0]; exact h

theorem popped_mem' (x : State) : (popped .x30 x).mem = x.mem := rfl

theorem freed_mem' (b : Nat) (x : State) : (freed b x).mem = x.mem := rfl

theorem rd8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem code_ok (c : PdChecked)
    (hsat : ∃ s, (Proof.RsaPkcs1Enc.encryptPrecomputedContract AArch64.abi (c.stack + 1088)).pre s)
    {s : State} (hp : RPre c.stack s) :
    WP isa (code (encName c) (encCode c)) s fun s' => abiPreserved s s' ∧ post s s' := by
  have hQ := Q_toNat hp
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 1088 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 1088 ≤ s.sp.toNat - 16
    omega
  · show WP isa (body (encName c) (encCode c)) (entered s) _
    refine WP.mono (body_ok c hsat hp) fun x ⟨hx, hpo⟩ => ?_
    have hsp' : (freed frameBytes x).sp = off (Q s) 1088 := by
      show x.sp + BitVec.ofNat 64 1088 = _; rw [hx.sp]
    refine ⟨⟨fun r hr => ?_, ?_, fun r hr => hx.vs r hr⟩, ?_⟩
    · rw [popped_gpr]
      by_cases h30 : r = .x30
      · subst h30
        simp only [ite_true]
        rw [hsp', freed_mem', rd8]
        exact hx.lr
      · simp only [h30, ite_false]; exact hx.cs r hr h30
    · show x.sp + BitVec.ofNat 64 1088 + 16 = s.sp
      rw [hx.sp, BitVec.add_assoc]
      exact Q_sp s
    · refine post_congr ?_ ?_ hpo
      · rw [popped_mem', freed_mem']
      · rw [popped_gpr, ite_eq_right_of_eq_false _ _ (by decide)]; rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
