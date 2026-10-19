module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyState
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Key generation's domain check, on its frame state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Whether the domain is one key generation accepts. -/
abbrev keygenChecked (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params

/-- After a call: the frame's bytes kept, the inputs kept, the callee-saved
registers kept. -/
theorem KeygenState.after_call {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    {wr : List Region} (ht : KeygenState h used t)
    (hwrF : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hwrP : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩)
    (hwrR : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩)
    (hf : Frame (wr ++ [below (randomBase s) extra]) t.mem u.mem)
    (hur : u.rd = t.rd) (huw : u.wr = t.wr) (husp : u.sp = t.sp) (huc : ∀ r ∈ preserved, u.gpr r = t.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) :
    KeygenState h used u ∧
      ∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
  have hb := keygen_call_frameBytes h hwrF hf
  have hw (d : Nat) (hd : d + 8 ≤ Random.frameBytes) := random_frame_words hb hd
  have hpl : (keygenInput s).params.length = (s.gpr .x4).toNat := bytesAt_length _ _ _
  have hrl : (keygenInput s).rand.length = (stackArg s 0).toNat := bytesAt_length _ _ _
  refine ⟨⟨ht.scr.congr huw, husp.trans ht.sp,
    ht.saved.congr (fun d _ hd => hw d (by unfold Random.frameBytes; omega)),
    (hw _ (by decide)).trans ht.usedWord, hur.trans ht.rd, huw.trans ht.wr,
    keygen_call_source ht.params hf hur huw (by rw [hpl]; exact hwrP) (by rw [hpl]; exact h.stackParams)
      (by rw [hpl]; exact Nat.le_of_lt (s.gpr .x4).isLt),
    keygen_call_source ht.rand hf hur huw (by rw [hrl]; exact hwrR) (by rw [hrl]; exact h.stackRand)
      (by rw [hrl]; exact Nat.le_of_lt (stackArg s 0).isLt),
    fun r hc => (huc r hc).trans (ht.callee r hc),
    fun r hc => (hv r hc).trans (ht.vectors r hc), (hw _ (by decide)).trans ht.link⟩, hw⟩

theorem keygen_restore_ok {s : State} {B : Addr} (hs : Scr s B Random.frameBytes)
    (hsp : s.sp = B) :
    WP isa (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0]) s fun t =>
      t.gpr .x30 = word s.mem B RandomSign.oLink ∧
      t.gpr .x0 = ((s.gpr .x0).setWidth 32).setWidth 64 ∧ t.mem = s.mem ∧ Keep [.x0, .x30] s t := by
  refine WP.mono (WP.keep [.x0, .x30] (Q := fun t =>
    t.gpr .x30 = word s.mem B RandomSign.oLink ∧
    t.gpr .x0 = ((s.gpr .x0).setWidth 32).setWidth 64 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hl, hx, hm⟩, hk⟩ => ⟨hl, hx, hm, hk⟩
  brun [exec_ldrSp_x', hsp, hs.ld (d := RandomSign.oLink) (by decide),
    exec_logic, State.read, State.write, BitVec.or_self]

theorem keygen_check_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t)
    (hdi : t.gpr .x0 = s.gpr .x3) (hsi : t.gpr .x1 = s.gpr .x4) (hdx : t.gpr .x2 = s.gpr .x5)
    (hcx : t.gpr .x3 = s.gpr .x6) (h8 : t.gpr .x4 = stackArg s 1) (h9 : t.gpr .x5 = stackArg s 2) :
    WP isa (.seq (.call (keygenCheckName v) (Generate.checkParameters v.mul))
      (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0])) t fun u =>
      KeygenState h 0 u ∧
      (∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d) ∧
      u.gpr .x0 = if keygenChecked s then 1 else 0 := by
  refine WP.seq (WP.mono (keygen_check_call v h ht.sp hdi hsi hdx hcx h8 h9 ht.rd ht.wr)
    fun u ⟨hur, huw, husp, huc, hf, hres, hv⟩ => ?_)
  have hscratch : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  have hwrs : ∀ r ∈ keygenCheckWr s, r.Disjoint ⟨randomBase s, Random.frameBytes⟩ := by
    intro r hr
    simp only [keygenCheckWr, List.mem_singleton] at hr
    subst hr
    exact hscratch
  have hul := (random_frame_words (keygen_call_frameBytes h hwrs hf) (d := RandomSign.oLink) (by decide)).trans ht.link
  refine WP.mono (keygen_restore_ok (ht.scr.congr huw) (husp.trans ht.sp))
    fun w ⟨hwl, hwx, hwm, hkw⟩ => ?_
  have hwc : ∀ r ∈ preserved, w.gpr r = t.gpr r := by
    intro r hr
    by_cases hl : r = .x30
    · subst r
      exact (hwl.trans hul).trans (ht.callee .x30 (by decide)).symm
    · exact (hkw.gpr r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)).trans (huc r hr hl)
  obtain ⟨hw, hwords⟩ := ht.after_call (wr := keygenCheckWr s) hwrs
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.paramsScratch.symm)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.randScratch.symm)
    (by rw [hwm]; exact hf) (hkw.rd.trans hur) (hkw.wr.trans huw) (hkw.sp.trans husp) hwc
    (fun r hr => (hkw.vcs r hr).trans (hv r hr))
  refine ⟨hw, hwords, ?_⟩
  have hp : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params := by
    apply List.ext_getElem (by simp only [keygenInput, bytesAt_length])
    intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact ht.params.val i h₂
  rw [hp] at hres
  rw [hwx]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth] at hres ⊢
  rw [hres]
  change (if keygenChecked s then 1 else 0) % 2 ^ 64 = (if keygenChecked s then (1 : BitVec 64) else 0).toNat
  cases keygenChecked s <;> rfl

end VG.Proof.Dsa.AArch64
