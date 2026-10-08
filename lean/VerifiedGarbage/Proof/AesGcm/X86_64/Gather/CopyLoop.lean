import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: gathering the slices

Untrusted: everything here is checked by Lean. `gatherCopy` walks the
descriptors as ChaCha20-Poly1305's `gather` does, with `copy` for each slice,
so its proofs are those of `Proof/ChaCha20Poly1305/X86_64/Gather/Loop.lean`
and `LoopCT.lean` (whose invariants, `GatherPre` and `GInv`, it shares) with
`copy_ok` for `copyBytes_ok`: the `cnt` slices copied to `Dst`
(`gatherCopy_wp`), and two runs whose descriptors agree, from states with
the same arguments, leak the same trace (`gatherCopy_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather VG.WriteBytes
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (next advance)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (GatherPre GInv NInv GKeeps gatherRegs next_wp advance_ok copyPre_of
  frame_of len_le gl_le cmp_ok Eq2 TT sb_agree sl_agree gl_agree)
open VG.Proof.AesGcm.X86_64 (length_bytesAt bytesAt_frame)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

section
variable {t u : State} {Src Dst : Addr} {cnt L i : Nat} (h : GatherPre t Src Dst cnt L)
include h

theorem restC_wp (hi : i < cnt) (hu : NInv t u Src Dst cnt i) :
    WP isa (.seq copy (.block advance)) u fun u' =>
      GInv t u' Src Dst cnt (i + 1) ∧ u'.zf = some (decide (i + 1 = cnt)) := by
  have hc := h.hcnt
  have hL := h.lt
  have hgl : gatheredLen 64 t.mem Src (i + 1) ≤ L := gl_le h (by omega)
  have hlen : (gathered 64 t.mem Src i).length = gatheredLen 64 t.mem Src i := Proof.Gcm.length_gathered _ _ _ _
  rw [ChaCha20Poly1305.X86_64.Gather.gl_succ] at hgl
  have hfr := frame_of (t := t) hu.mem (len_le h (Nat.le_of_lt hi))
  have hsd := h.lsd _ (ChaCha20Poly1305.X86_64.Gather.slice_mem t.mem Src hi)
  have hcp := copyPre_of h hi hu
  refine WP.seq (WP.mono (copy_ok hcp) fun u₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.mono (advance_ok u₂ (D := Dst + BitVec.ofNat 64 (gatheredLen 64 t.mem Src i))
    (n := ChaCha20Poly1305.X86_64.Gather.sl t.mem Src i) (k := cnt - i)
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.rdi])
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.rcx])
    (by rw [g₂ _ (by decide) (by decide) (by decide), hu.r9]) (by omega) (by omega))
    fun u₃ ⟨rdi₃, r9₃, zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_
  have hbytes : bytesAt u.mem (ChaCha20Poly1305.X86_64.Gather.sb t.mem Src i)
      (ChaCha20Poly1305.X86_64.Gather.sl t.mem Src i) =
      bytesAt t.mem (ChaCha20Poly1305.X86_64.Gather.sb t.mem Src i) (ChaCha20Poly1305.X86_64.Gather.sl t.mem Src i) := by
    refine bytesAt_frame hfr (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨⟨?_, ?_, ?_, ?_, hu.keep.trans ⟨fun r hr => ?_, rd₃.trans rd₂, wr₃.trans wr₂⟩⟩, ?_⟩
  · rw [g₃ _ (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide), hu.r11]
  · rw [r9₃, Nat.sub_sub]
  · rw [rdi₃, BitVec.add_assoc, ← BitVec.ofNat_add, ← ChaCha20Poly1305.X86_64.Gather.gl_succ]
  · rw [m₃, m₂, hbytes, hu.mem, ChaCha20Poly1305.X86_64.Gather.pt_succ, ← hlen,
      writeBytes_append _ _ _ _ (by rw [hlen, length_bytesAt]; omega)]
  · simp only [gatherRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hr
    rw [g₃ r h₄ h₆, g₂ r h₁ h₅ h₇]
  · rw [zf₃]; congr 1; simp only [decide_eq_decide]; omega

/-- One iteration of the loop. -/
theorem bodyC_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.seq (.block next) (.seq copy (.block advance))) u fun u' =>
      GInv t u' Src Dst cnt (i + 1) ∧ u'.zf = some (decide (i + 1 = cnt)) :=
  WP.seq (WP.mono (next_wp h hi hu) fun _ h₁ => restC_wp h hi h₁)

end

/-- `gatherCopy`: the `cnt` slices copied to `Dst`. -/
theorem gatherCopy_wp (t : State) {Src Dst : Addr} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gatherCopy t fun t' => t'.mem = writeBytes t.mem Dst (gathered 64 t.mem Src cnt) ∧ GKeeps t t' := by
  have hc := h.hcnt
  refine WP.seq (WP.mono (cmp_ok t h.r9 h.hcnt) fun t₁ ⟨z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have h' : GatherPre t₁ Src Dst cnt L := h.of_eq g₁ m₁ rd₁ wr₁
  have kp : GKeeps t t₁ := ⟨fun r _ => by rw [g₁], rd₁, wr₁⟩
  refine WP.ite (decide (cnt = 0)) (by show t₁.zf = _; exact z₁) (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by rw [m₁]; simp [gathered, Sig.listed, writeBytes_nil], kp⟩
  · have hpos : cnt ≠ 0 := by simpa using hf
    refine WP.mono (Q := fun (u : State) => u.mem = writeBytes t₁.mem Dst (gathered 64 t₁.mem Src cnt) ∧ GKeeps t₁ u) ?_
      fun t' ⟨m', k'⟩ => ⟨by rw [m', m₁], kp.trans k'⟩
    refine WP.loop (M := isa) (c := .ne)
      (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t₁ u Src Dst cnt i) ?_ (cnt - 0) _
      ⟨0, rfl, by omega, GInv.init h'⟩
    rintro w u ⟨i, rfl, hi, hu⟩
    refine WP.mono (bodyC_wp h' hi hu) fun u₃ ⟨h₃, z₃⟩ => ?_
    have ev : isa.eval .ne u₃ = some !decide (i + 1 = cnt) := by show u₃.zf.map (!·) = _; rw [z₃]; rfl
    by_cases he : i + 1 = cnt
    · left
      exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
    · right
      exact ⟨by rw [ev]; simp [he], cnt - (i + 1), by omega, i + 1, rfl, by omega, h₃⟩

/-! ## Two runs -/

theorem copy_check : ∃ hc, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx]) copy hc).isSome = true :=
  ⟨_, by unfold copy copy64Body copy16Body copy1Body srcD dstD; taint_decide⟩

section
variable {t₁ t₂ : State} {Src Dst : Addr} {cnt L : Nat}
  (hd : ∀ j < cnt * 16, t₁.mem (Src + BitVec.ofNat 64 j) = t₂.mem (Src + BitVec.ofNat 64 j))
  (h₁ : GatherPre t₁ Src Dst cnt L) (h₂ : GatherPre t₂ Src Dst cnt L)
include hd h₁ h₂

/-- One iteration of the loop, in two runs. -/
theorem bodyC_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copy (.block advance)))
      (fun u₁ u₂ => (GInv t₁ u₁ Src Dst cnt (i + 1) ∧ u₁.zf = some (decide (i + 1 = cnt))) ∧
        (GInv t₂ u₂ Src Dst cnt (i + 1) ∧ u₂.zf = some (decide (i + 1 = cnt)))) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copy (.block advance))) TT := by
    intro σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨g₁, g₂⟩ e₁ e₂
    refine ChaCha20Poly1305.X86_64.Gather.rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [g₁.r11, g₂.r11]) ⟨_, by unfold next; taint_decide⟩)
      (next_wp h₁ hi g₁) (next_wp h₂ hi g₂) (fun τ₁ τ₂ n₁ n₂ => ?_) σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨rfl, rfl⟩ e₁ e₂
    have p₁ := copyPre_of h₁ hi n₁
    have p₂ := copyPre_of h₂ hi n₂
    rw [← sb_agree hd hi, ← sl_agree hd hi, ← gl_agree hd (Nat.le_of_lt hi)] at p₂
    refine ChaCha20Poly1305.X86_64.Gather.rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsi, .rdi, .rcx] (by simp [p₁.rsi, p₂.rsi, p₁.rdi, p₂.rdi, p₁.rcx, p₂.rcx])
      copy_check) (copy_ok p₁) (copy_ok p₂) fun v₁ v₂ c₁ c₂ => ?_
    refine ChaCha20Poly1305.X86_64.Gather.rel_regs [.rdi, .rcx, .r9] ?_ ⟨_, by unfold advance; taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨by rw [c₁.2.1 _ (by decide) (by decide) (by decide), c₂.2.1 _ (by decide) (by decide) (by decide),
        p₁.rdi, p₂.rdi], by rw [c₁.2.1 _ (by decide) (by decide) (by decide),
        c₂.2.1 _ (by decide) (by decide) (by decide), p₁.rcx, p₂.rcx], ?_⟩
    rw [c₁.2.1 _ (by decide) (by decide) (by decide), c₂.2.1 _ (by decide) (by decide) (by decide), n₁.r9, n₂.r9]
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ => ⟨bodyC_wp h₁ hi g₁, bodyC_wp h₂ hi g₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- `gatherCopy`, in two runs. -/
theorem gatherCopy_rel : RelCT isa (Eq2 t₁ t₂) gatherCopy TT := by
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r9] (by simp [h₁.r9, h₂.r9]) ⟨_, by taint_decide⟩)
    (cmp_ok t₁ h₁.r9 h₁.hcnt) (cmp_ok t₂ h₂.r9 h₂.hcnt) fun τ₁ τ₂ ⟨z₁, g₁, m₁, rd₁, wr₁⟩ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  refine ChaCha20Poly1305.X86_64.Gather.rel_ite (b := decide (cnt = 0)) z₁ z₂ (fun _ => ChaCha20Poly1305.X86_64.Gather.rel_skip) fun hf => ?_
  have hpos : cnt ≠ 0 := by simpa using hf
  have hd' : ∀ j < cnt * 16, τ₁.mem (Src + BitVec.ofNat 64 j) = τ₂.mem (Src + BitVec.ofNat 64 j) := by
    rw [m₁, m₂]; exact hd
  have h₁' := h₁.of_eq g₁ m₁ rd₁ wr₁
  have h₂' := h₂.of_eq g₂ m₂ rd₂ wr₂
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv τ₁ u₁ Src Dst cnt i ∧ GInv τ₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega, GInv.init h₁', GInv.init h₂'⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (bodyC_rel hd' h₁' h₂' hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩
    have ev₁ : isa.eval .ne u₁ = some !decide (i + 1 = cnt) := by show u₁.zf.map (!·) = _; rw [z₁]; rfl
    have ev₂ : isa.eval .ne u₂ = some !decide (i + 1 = cnt) := by show u₂.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega
    exact ⟨cnt - (i + 1), by omega, i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

end

end VG.Proof.AesGcm.X86_64.Gather
